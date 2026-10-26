import V185TrunkScan23Chunk0490

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2904805 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 5]
def baseStart_2904805 : Nat := 118140960795 + 2904805 * 2 ^ 59
def prefixEnd_2904805 : Nat := 4983230072969 + 3 ^ 40 * 2904805 * 2
def baseEnd_2904805 : Nat := 165729019175956963419839

theorem tailTrace_2904805 : CollatzResearch.WordTrace tailWord_2904805 prefixEnd_2904805 165729019175956963419839 := by
  unfold tailWord_2904805
  simp only [CollatzResearch.WordTrace]
  refine ⟨105946942241395061042475869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70631294827596707361650579 105946942241395061042475869)
  ·
    refine ⟨39730103340523147890928451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105946942241395061042475869 39730103340523147890928451)
    ·
      refine ⟨59595155010784721836392677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39730103340523147890928451 59595155010784721836392677)
      ·
        refine ⟨11174091564522135344323627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59595155010784721836392677 11174091564522135344323627)
        ·
          refine ⟨16761137346783203016485441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174091564522135344323627 16761137346783203016485441)
          ·
            refine ⟨12570853010087402262364081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16761137346783203016485441 12570853010087402262364081)
            ·
              refine ⟨9428139757565551696773061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12570853010087402262364081 9428139757565551696773061)
              ·
                refine ⟨1767776204543540943144949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9428139757565551696773061 1767776204543540943144949)
                ·
                  refine ⟨165729019175956963419839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767776204543540943144949 165729019175956963419839)
                  ·
                    rfl

theorem cell23_2904805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_2904805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904805 prefixEnd_2904805 := by exact prefixLift 2904805
  have htrace : WordTrace (prefixWord ++ tailWord_2904805) baseStart_2904805 baseEnd_2904805 := by
    simpa [prefixWord, tailWord_2904805, baseEnd_2904805] using wordTrace_append hprefix tailTrace_2904805
  have hstable : (prefixWord ++ tailWord_2904805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904805).length < 2 ^ (prefixWord ++ tailWord_2904805).sum := by decide
  have hdescent : baseEnd_2904805 < baseStart_2904805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904811 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_2904811 : Nat := 118140960795 + 2904811 * 2 ^ 59
def prefixEnd_2904811 : Nat := 4983230072969 + 3 ^ 40 * 2904811 * 2
def baseEnd_2904811 : Nat := 1491564253467539647303523

theorem tailTrace_2904811 : CollatzResearch.WordTrace tailWord_2904811 prefixEnd_2904811 1491564253467539647303523 := by
  unfold tailWord_2904811
  simp only [CollatzResearch.WordTrace]
  refine ⟨105947161079373324067194287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70631440719582216044796191 105947161079373324067194287)
  ·
    refine ⟨158920741619059986100791431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105947161079373324067194287 158920741619059986100791431)
    ·
      refine ⟨238381112428589979151187147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158920741619059986100791431 238381112428589979151187147)
      ·
        refine ⟨357571668642884968726780721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238381112428589979151187147 357571668642884968726780721)
        ·
          refine ⟨268178751482163726545085541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357571668642884968726780721 268178751482163726545085541)
          ·
            refine ⟨50283515902905698727203539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268178751482163726545085541 50283515902905698727203539)
            ·
              refine ⟨75425273854358548090805309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50283515902905698727203539 75425273854358548090805309)
              ·
                refine ⟨28284477695384455534051991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75425273854358548090805309 28284477695384455534051991)
                ·
                  refine ⟨42426716543076683301077987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28284477695384455534051991 42426716543076683301077987)
                  ·
                    refine ⟨63640074814615024951616981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42426716543076683301077987 63640074814615024951616981)
                    ·
                      refine ⟨1491564253467539647303523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63640074814615024951616981 1491564253467539647303523)
                      ·
                        rfl

theorem cell23_2904811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_2904811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904811 prefixEnd_2904811 := by exact prefixLift 2904811
  have htrace : WordTrace (prefixWord ++ tailWord_2904811) baseStart_2904811 baseEnd_2904811 := by
    simpa [prefixWord, tailWord_2904811, baseEnd_2904811] using wordTrace_append hprefix tailTrace_2904811
  have hstable : (prefixWord ++ tailWord_2904811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904811).length < 2 ^ (prefixWord ++ tailWord_2904811).sum := by decide
  have hdescent : baseEnd_2904811 < baseStart_2904811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904818 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_2904818 : Nat := 118140960795 + 2904818 * 2 ^ 59
def prefixEnd_2904818 : Nat := 4983230072969 + 3 ^ 40 * 2904818 * 2
def baseEnd_2904818 : Nat := 497189282610707039971997

theorem tailTrace_2904818 : CollatzResearch.WordTrace tailWord_2904818 prefixEnd_2904818 497189282610707039971997 := by
  unfold tailWord_2904818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26486854097586991065674777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70631610926898642841799405 26486854097586991065674777)
  ·
    refine ⟨19865140573190243299256083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26486854097586991065674777 19865140573190243299256083)
    ·
      refine ⟨29797710859785364948884125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19865140573190243299256083 29797710859785364948884125)
      ·
        refine ⟨11174141572419511855831547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29797710859785364948884125 11174141572419511855831547)
        ·
          refine ⟨16761212358629267783747321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174141572419511855831547 16761212358629267783747321)
          ·
            refine ⟨12570909268971950837810491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16761212358629267783747321 12570909268971950837810491)
            ·
              refine ⟨18856363903457926256715737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12570909268971950837810491 18856363903457926256715737)
              ·
                refine ⟨14142272927593444692536803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18856363903457926256715737 14142272927593444692536803)
                ·
                  refine ⟨21213409391390167038805205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14142272927593444692536803 21213409391390167038805205)
                  ·
                    refine ⟨497189282610707039971997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21213409391390167038805205 497189282610707039971997)
                    ·
                      rfl

theorem cell23_2904818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_2904818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904818 prefixEnd_2904818 := by exact prefixLift 2904818
  have htrace : WordTrace (prefixWord ++ tailWord_2904818) baseStart_2904818 baseEnd_2904818 := by
    simpa [prefixWord, tailWord_2904818, baseEnd_2904818] using wordTrace_append hprefix tailTrace_2904818
  have hstable : (prefixWord ++ tailWord_2904818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904818).length < 2 ^ (prefixWord ++ tailWord_2904818).sum := by decide
  have hdescent : baseEnd_2904818 < baseStart_2904818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904831 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 10]
def baseStart_2904831 : Nat := 118140960795 + 2904831 * 2 ^ 59
def prefixEnd_2904831 : Nat := 4983230072969 + 3 ^ 40 * 2904831 * 2
def baseEnd_2904831 : Nat := 497191507693543189684477

theorem tailTrace_2904831 : CollatzResearch.WordTrace tailWord_2904831 prefixEnd_2904831 497191507693543189684477 := by
  unfold tailWord_2904831
  simp only [CollatzResearch.WordTrace]
  refine ⟨105947890539300867482922347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70631927026200578321948231 105947890539300867482922347)
  ·
    refine ⟨158921835808951301224383521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105947890539300867482922347 158921835808951301224383521)
    ·
      refine ⟨119191376856713475918287641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158921835808951301224383521 119191376856713475918287641)
      ·
        refine ⟨89393532642535106938715731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119191376856713475918287641 89393532642535106938715731)
        ·
          refine ⟨134090298963802660408073597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89393532642535106938715731 134090298963802660408073597)
          ·
            refine ⟨50283862111425997653027599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134090298963802660408073597 50283862111425997653027599)
            ·
              refine ⟨75425793167138996479541399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50283862111425997653027599 75425793167138996479541399)
              ·
                refine ⟨113138689750708494719312099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75425793167138996479541399 113138689750708494719312099)
                ·
                  refine ⟨169708034626062742078968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113138689750708494719312099 169708034626062742078968149)
                  ·
                    refine ⟨497191507693543189684477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 169708034626062742078968149 497191507693543189684477)
                    ·
                      rfl

theorem cell23_2904831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_2904831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904831 prefixEnd_2904831 := by exact prefixLift 2904831
  have htrace : WordTrace (prefixWord ++ tailWord_2904831) baseStart_2904831 baseEnd_2904831 := by
    simpa [prefixWord, tailWord_2904831, baseEnd_2904831] using wordTrace_append hprefix tailTrace_2904831
  have hstable : (prefixWord ++ tailWord_2904831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904831).length < 2 ^ (prefixWord ++ tailWord_2904831).sum := by decide
  have hdescent : baseEnd_2904831 < baseStart_2904831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904945 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2904945 : Nat := 118140960795 + 2904945 * 2 ^ 59
def prefixEnd_2904945 : Nat := 4983230072969 + 3 ^ 40 * 2904945 * 2
def baseEnd_2904945 : Nat := 1491633059875242123027907

theorem tailTrace_2904945 : CollatzResearch.WordTrace tailWord_2904945 prefixEnd_2904945 1491633059875242123027907 := by
  unfold tailWord_2904945
  simp only [CollatzResearch.WordTrace]
  refine ⟨105952048460887864952572289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70634698973925243301714859 105952048460887864952572289)
  ·
    refine ⟨79464036345665898714429217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105952048460887864952572289 79464036345665898714429217)
    ·
      refine ⟨59598027259249424035821913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79464036345665898714429217 59598027259249424035821913)
      ·
        refine ⟨44698520444437068026866435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59598027259249424035821913 44698520444437068026866435)
        ·
          refine ⟨67047780666655602040299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44698520444437068026866435 67047780666655602040299653)
          ·
            refine ⟨12571458874997925382556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67047780666655602040299653 12571458874997925382556185)
            ·
              refine ⟨9428594156248444036917139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12571458874997925382556185 9428594156248444036917139)
              ·
                refine ⟨14142891234372666055375709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9428594156248444036917139 14142891234372666055375709)
                ·
                  refine ⟨5303584212889749770765891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14142891234372666055375709 5303584212889749770765891)
                  ·
                    refine ⟨7955376319334624656148837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5303584212889749770765891 7955376319334624656148837)
                    ·
                      refine ⟨1491633059875242123027907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7955376319334624656148837 1491633059875242123027907)
                      ·
                        rfl

theorem cell23_2904945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2904945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904945 prefixEnd_2904945 := by exact prefixLift 2904945
  have htrace : WordTrace (prefixWord ++ tailWord_2904945) baseStart_2904945 baseEnd_2904945 := by
    simpa [prefixWord, tailWord_2904945, baseEnd_2904945] using wordTrace_append hprefix tailTrace_2904945
  have hstable : (prefixWord ++ tailWord_2904945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904945).length < 2 ^ (prefixWord ++ tailWord_2904945).sum := by decide
  have hdescent : baseEnd_2904945 < baseStart_2904945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904949 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2904949 : Nat := 118140960795 + 2904949 * 2 ^ 59
def prefixEnd_2904949 : Nat := 4983230072969 + 3 ^ 40 * 2904949 * 2
def baseEnd_2904949 : Nat := 1491635113797860107377889

theorem tailTrace_2904949 : CollatzResearch.WordTrace tailWord_2904949 prefixEnd_2904949 1491635113797860107377889 := by
  unfold tailWord_2904949
  simp only [CollatzResearch.WordTrace]
  refine ⟨105952194352873373635717901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70634796235248915757145267 105952194352873373635717901)
  ·
    refine ⟨39732072882327515113394213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105952194352873373635717901 39732072882327515113394213)
    ·
      refine ⟨7449763665436409083761415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39732072882327515113394213 7449763665436409083761415)
      ·
        refine ⟨11174645498154613625642123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7449763665436409083761415 11174645498154613625642123)
        ·
          refine ⟨16761968247231920438463185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174645498154613625642123 16761968247231920438463185)
          ·
            refine ⟨12571476185423940328847389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16761968247231920438463185 12571476185423940328847389)
            ·
              refine ⟨4714303569533977623317771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12571476185423940328847389 4714303569533977623317771)
              ·
                refine ⟨7071455354300966434976657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714303569533977623317771 7071455354300966434976657)
                ·
                  refine ⟨5303591515725724826232493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071455354300966434976657 5303591515725724826232493)
                  ·
                    refine ⟨1988846818397146809837185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5303591515725724826232493 1988846818397146809837185)
                    ·
                      refine ⟨1491635113797860107377889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988846818397146809837185 1491635113797860107377889)
                      ·
                        rfl

theorem cell23_2904949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2904949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904949 prefixEnd_2904949 := by exact prefixLift 2904949
  have htrace : WordTrace (prefixWord ++ tailWord_2904949) baseStart_2904949 baseEnd_2904949 := by
    simpa [prefixWord, tailWord_2904949, baseEnd_2904949] using wordTrace_append hprefix tailTrace_2904949
  have hstable : (prefixWord ++ tailWord_2904949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904949).length < 2 ^ (prefixWord ++ tailWord_2904949).sum := by decide
  have hdescent : baseEnd_2904949 < baseStart_2904949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904972 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_2904972 : Nat := 118140960795 + 2904972 * 2 ^ 59
def prefixEnd_2904972 : Nat := 4983230072969 + 3 ^ 40 * 2904972 * 2
def baseEnd_2904972 : Nat := 497215641284304505796761

theorem tailTrace_2904972 : CollatzResearch.WordTrace tailWord_2904972 prefixEnd_2904972 497215641284304505796761 := by
  unfold tailWord_2904972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52976516615895024281902585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70635355487860032375870113 52976516615895024281902585)
  ·
    refine ⟨39732387461921268211426939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52976516615895024281902585 39732387461921268211426939)
    ·
      refine ⟨59598581192881902317140409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39732387461921268211426939 59598581192881902317140409)
      ·
        refine ⟨44698935894661426737855307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59598581192881902317140409 44698935894661426737855307)
        ·
          refine ⟨67048403841992140106782961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44698935894661426737855307 67048403841992140106782961)
          ·
            refine ⟨50286302881494105080087221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67048403841992140106782961 50286302881494105080087221)
            ·
              refine ⟨4714340895140072351258177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50286302881494105080087221 4714340895140072351258177)
              ·
                refine ⟨3535755671355054263443633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714340895140072351258177 3535755671355054263443633)
                ·
                  refine ⟨2651816753516290697582725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535755671355054263443633 2651816753516290697582725)
                  ·
                    refine ⟨497215641284304505796761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2651816753516290697582725 497215641284304505796761)
                    ·
                      rfl

theorem cell23_2904972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_2904972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904972 prefixEnd_2904972 := by exact prefixLift 2904972
  have htrace : WordTrace (prefixWord ++ tailWord_2904972) baseStart_2904972 baseEnd_2904972 := by
    simpa [prefixWord, tailWord_2904972, baseEnd_2904972] using wordTrace_append hprefix tailTrace_2904972
  have hstable : (prefixWord ++ tailWord_2904972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904972).length < 2 ^ (prefixWord ++ tailWord_2904972).sum := by decide
  have hdescent : baseEnd_2904972 < baseStart_2904972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904989 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2904989 : Nat := 118140960795 + 2904989 * 2 ^ 59
def prefixEnd_2904989 : Nat := 4983230072969 + 3 ^ 40 * 2904989 * 2
def baseEnd_2904989 : Nat := 497218551008013316959235

theorem tailTrace_2904989 : CollatzResearch.WordTrace tailWord_2904989 prefixEnd_2904989 497218551008013316959235 := by
  unfold tailWord_2904989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105953653272728460467174021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70635768848485640311449347 105953653272728460467174021)
  ·
    refine ⟨19866309988636586337595129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105953653272728460467174021 19866309988636586337595129)
    ·
      refine ⟨14899732491477439753196347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19866309988636586337595129 14899732491477439753196347)
      ·
        refine ⟨22349598737216159629794521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14899732491477439753196347 22349598737216159629794521)
        ·
          refine ⟨16762199052912119722345891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22349598737216159629794521 16762199052912119722345891)
          ·
            refine ⟨25143298579368179583518837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16762199052912119722345891 25143298579368179583518837)
            ·
              refine ⟨2357184241815766835954891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25143298579368179583518837 2357184241815766835954891)
              ·
                refine ⟨3535776362723650253932337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357184241815766835954891 3535776362723650253932337)
                ·
                  refine ⟨2651832272042737690449253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535776362723650253932337 2651832272042737690449253)
                  ·
                    refine ⟨497218551008013316959235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2651832272042737690449253 497218551008013316959235)
                    ·
                      rfl

theorem cell23_2904989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2904989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904989 prefixEnd_2904989 := by exact prefixLift 2904989
  have htrace : WordTrace (prefixWord ++ tailWord_2904989) baseStart_2904989 baseEnd_2904989 := by
    simpa [prefixWord, tailWord_2904989, baseEnd_2904989] using wordTrace_append hprefix tailTrace_2904989
  have hstable : (prefixWord ++ tailWord_2904989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904989).length < 2 ^ (prefixWord ++ tailWord_2904989).sum := by decide
  have hdescent : baseEnd_2904989 < baseStart_2904989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905102 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2905102 : Nat := 118140960795 + 2905102 * 2 ^ 59
def prefixEnd_2905102 : Nat := 4983230072969 + 3 ^ 40 * 2905102 * 2
def baseEnd_2905102 : Nat := 1491713676337998008764685

theorem tailTrace_2905102 : CollatzResearch.WordTrace tailWord_2905102 prefixEnd_2905102 1491713676337998008764685 := by
  unfold tailWord_2905102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244721840164885095754695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70638516480879387177358373 13244721840164885095754695)
  ·
    refine ⟨19867082760247327643632043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244721840164885095754695 19867082760247327643632043)
    ·
      refine ⟨29800624140370991465448065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19867082760247327643632043 29800624140370991465448065)
      ·
        refine ⟨22350468105278243599086049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29800624140370991465448065 22350468105278243599086049)
        ·
          refine ⟨16762851078958682699314537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22350468105278243599086049 16762851078958682699314537)
          ·
            refine ⟨12572138309219012024485903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16762851078958682699314537 12572138309219012024485903)
            ·
              refine ⟨18858207463828518036728855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572138309219012024485903 18858207463828518036728855)
              ·
                refine ⟨28287311195742777055093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18858207463828518036728855 28287311195742777055093283)
                ·
                  refine ⟨42430966793614165582639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28287311195742777055093283 42430966793614165582639925)
                  ·
                    refine ⟨3977903136901328023372493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42430966793614165582639925 3977903136901328023372493)
                    ·
                      refine ⟨1491713676337998008764685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3977903136901328023372493 1491713676337998008764685)
                      ·
                        rfl

theorem cell23_2905102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2905102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905102 prefixEnd_2905102 := by exact prefixLift 2905102
  have htrace : WordTrace (prefixWord ++ tailWord_2905102) baseStart_2905102 baseEnd_2905102 := by
    simpa [prefixWord, tailWord_2905102, baseEnd_2905102] using wordTrace_append hprefix tailTrace_2905102
  have hstable : (prefixWord ++ tailWord_2905102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905102).length < 2 ^ (prefixWord ++ tailWord_2905102).sum := by decide
  have hdescent : baseEnd_2905102 < baseStart_2905102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905105 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2905105 : Nat := 118140960795 + 2905105 * 2 ^ 59
def prefixEnd_2905105 : Nat := 4983230072969 + 3 ^ 40 * 2905105 * 2
def baseEnd_2905105 : Nat := 497238405593320499009057

theorem tailTrace_2905105 : CollatzResearch.WordTrace tailWord_2905105 prefixEnd_2905105 497238405593320499009057 := by
  unfold tailWord_2905105
  simp only [CollatzResearch.WordTrace]
  refine ⟨105957884140308212278396769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70638589426872141518931179 105957884140308212278396769)
  ·
    refine ⟨79468413105231159208797577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105957884140308212278396769 79468413105231159208797577)
    ·
      refine ⟨59601309828923369406598183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79468413105231159208797577 59601309828923369406598183)
      ·
        refine ⟨89401964743385054109897275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59601309828923369406598183 89401964743385054109897275)
        ·
          refine ⟨134102947115077581164845913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89401964743385054109897275 134102947115077581164845913)
          ·
            refine ⟨100577210336308185873634435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134102947115077581164845913 100577210336308185873634435)
            ·
              refine ⟨150865815504462278810451653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100577210336308185873634435 150865815504462278810451653)
              ·
                refine ⟨28287340407086677276959685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150865815504462278810451653 28287340407086677276959685)
                ·
                  refine ⟨5303876326328751989429941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28287340407086677276959685 5303876326328751989429941)
                  ·
                    refine ⟨497238405593320499009057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5303876326328751989429941 497238405593320499009057)
                    ·
                      rfl

theorem cell23_2905105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2905105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905105 prefixEnd_2905105 := by exact prefixLift 2905105
  have htrace : WordTrace (prefixWord ++ tailWord_2905105) baseStart_2905105 baseEnd_2905105 := by
    simpa [prefixWord, tailWord_2905105, baseEnd_2905105] using wordTrace_append hprefix tailTrace_2905105
  have hstable : (prefixWord ++ tailWord_2905105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905105).length < 2 ^ (prefixWord ++ tailWord_2905105).sum := by decide
  have hdescent : baseEnd_2905105 < baseStart_2905105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905122 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2905122 : Nat := 118140960795 + 2905122 * 2 ^ 59
def prefixEnd_2905122 : Nat := 4983230072969 + 3 ^ 40 * 2905122 * 2
def baseEnd_2905122 : Nat := 497241315317029310171531

theorem tailTrace_2905122 : CollatzResearch.WordTrace tailWord_2905122 prefixEnd_2905122 497241315317029310171531 := by
  unfold tailWord_2905122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489626045311656045441405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70639002787497749454510413 26489626045311656045441405)
  ·
    refine ⟨9933609766991871017040527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26489626045311656045441405 9933609766991871017040527)
    ·
      refine ⟨14900414650487806525560791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933609766991871017040527 14900414650487806525560791)
      ·
        refine ⟨22350621975731709788341187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14900414650487806525560791 22350621975731709788341187)
        ·
          refine ⟨33525932963597564682511781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22350621975731709788341187 33525932963597564682511781)
          ·
            refine ⟨6286112430674543377970959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33525932963597564682511781 6286112430674543377970959)
            ·
              refine ⟨9429168646011815066956439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286112430674543377970959 9429168646011815066956439)
              ·
                refine ⟨14143752969017722600434659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429168646011815066956439 14143752969017722600434659)
                ·
                  refine ⟨21215629453526583900651989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14143752969017722600434659 21215629453526583900651989)
                  ·
                    refine ⟨497241315317029310171531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21215629453526583900651989 497241315317029310171531)
                    ·
                      rfl

theorem cell23_2905122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2905122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905122 prefixEnd_2905122 := by exact prefixLift 2905122
  have htrace : WordTrace (prefixWord ++ tailWord_2905122) baseStart_2905122 baseEnd_2905122 := by
    simpa [prefixWord, tailWord_2905122, baseEnd_2905122] using wordTrace_append hprefix tailTrace_2905122
  have hstable : (prefixWord ++ tailWord_2905122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905122).length < 2 ^ (prefixWord ++ tailWord_2905122).sum := by decide
  have hdescent : baseEnd_2905122 < baseStart_2905122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905155 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_2905155 : Nat := 118140960795 + 2905155 * 2 ^ 59
def prefixEnd_2905155 : Nat := 4983230072969 + 3 ^ 40 * 2905155 * 2
def baseEnd_2905155 : Nat := 1491740890812686301401941

theorem tailTrace_2905155 : CollatzResearch.WordTrace tailWord_2905155 prefixEnd_2905155 1491740890812686301401941 := by
  unfold tailWord_2905155
  simp only [CollatzResearch.WordTrace]
  refine ⟨105959707790127070817716919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70639805193418047211811279 105959707790127070817716919)
  ·
    refine ⟨158939561685190606226575379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105959707790127070817716919 158939561685190606226575379)
    ·
      refine ⟨238409342527785909339863069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158939561685190606226575379 238409342527785909339863069)
      ·
        refine ⟨89403503447919716002448651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238409342527785909339863069 89403503447919716002448651)
        ·
          refine ⟨134105255171879574003672977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89403503447919716002448651 134105255171879574003672977)
          ·
            refine ⟨100578941378909680502754733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134105255171879574003672977 100578941378909680502754733)
            ·
              refine ⟨37717103017091130188533025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100578941378909680502754733 37717103017091130188533025)
              ·
                refine ⟨28287827262818347641399769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37717103017091130188533025 28287827262818347641399769)
                ·
                  refine ⟨21215870447113760731049827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28287827262818347641399769 21215870447113760731049827)
                  ·
                    refine ⟨31823805670670641096574741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21215870447113760731049827 31823805670670641096574741)
                    ·
                      refine ⟨1491740890812686301401941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31823805670670641096574741 1491740890812686301401941)
                      ·
                        rfl

theorem cell23_2905155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_2905155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905155 prefixEnd_2905155 := by exact prefixLift 2905155
  have htrace : WordTrace (prefixWord ++ tailWord_2905155) baseStart_2905155 baseEnd_2905155 := by
    simpa [prefixWord, tailWord_2905155, baseEnd_2905155] using wordTrace_append hprefix tailTrace_2905155
  have hstable : (prefixWord ++ tailWord_2905155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905155).length < 2 ^ (prefixWord ++ tailWord_2905155).sum := by decide
  have hdescent : baseEnd_2905155 < baseStart_2905155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905159 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_2905159 : Nat := 118140960795 + 2905159 * 2 ^ 59
def prefixEnd_2905159 : Nat := 4983230072969 + 3 ^ 40 * 2905159 * 2
def baseEnd_2905159 : Nat := 1491742944735304285751923

theorem tailTrace_2905159 : CollatzResearch.WordTrace tailWord_2905159 prefixEnd_2905159 1491742944735304285751923 := by
  unfold tailWord_2905159
  simp only [CollatzResearch.WordTrace]
  refine ⟨105959853682112579500862531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70639902454741719667241687 105959853682112579500862531)
  ·
    refine ⟨158939780523168869251293797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105959853682112579500862531 158939780523168869251293797)
    ·
      refine ⟨29801208848094162984617587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158939780523168869251293797 29801208848094162984617587)
      ·
        refine ⟨44701813272141244476926381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801208848094162984617587 44701813272141244476926381)
        ·
          refine ⟨16763179977052966678847393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44701813272141244476926381 16763179977052966678847393)
          ·
            refine ⟨12572384982789725009135545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16763179977052966678847393 12572384982789725009135545)
            ·
              refine ⟨9429288737092293756851659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12572384982789725009135545 9429288737092293756851659)
              ·
                refine ⟨14143933105638440635277489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429288737092293756851659 14143933105638440635277489)
                ·
                  refine ⟨10607949829228830476458117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14143933105638440635277489 10607949829228830476458117)
                  ·
                    refine ⟨1988990592980405714335897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10607949829228830476458117 1988990592980405714335897)
                    ·
                      refine ⟨1491742944735304285751923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988990592980405714335897 1491742944735304285751923)
                      ·
                        rfl

theorem cell23_2905159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_2905159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905159 prefixEnd_2905159 := by exact prefixLift 2905159
  have htrace : WordTrace (prefixWord ++ tailWord_2905159) baseStart_2905159 baseEnd_2905159 := by
    simpa [prefixWord, tailWord_2905159, baseEnd_2905159] using wordTrace_append hprefix tailTrace_2905159
  have hstable : (prefixWord ++ tailWord_2905159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905159).length < 2 ^ (prefixWord ++ tailWord_2905159).sum := by decide
  have hdescent : baseEnd_2905159 < baseStart_2905159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905162 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_2905162 : Nat := 118140960795 + 2905162 * 2 ^ 59
def prefixEnd_2905162 : Nat := 4983230072969 + 3 ^ 40 * 2905162 * 2
def baseEnd_2905162 : Nat := 1491744485177267774014409

theorem tailTrace_2905162 : CollatzResearch.WordTrace tailWord_2905162 prefixEnd_2905162 1491744485177267774014409 := by
  unfold tailWord_2905162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489990775275427753305435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70639975400734474008814493 26489990775275427753305435)
  ·
    refine ⟨39734986162913141629958153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489990775275427753305435 39734986162913141629958153)
    ·
      refine ⟨29801239622184856222468615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39734986162913141629958153 29801239622184856222468615)
      ·
        refine ⟨44701859433277284333702923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801239622184856222468615 44701859433277284333702923)
        ·
          refine ⟨67052789149915926500554385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44701859433277284333702923 67052789149915926500554385)
          ·
            refine ⟨50289591862436944875415789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67052789149915926500554385 50289591862436944875415789)
            ·
              refine ⟨18858596948413854328280921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50289591862436944875415789 18858596948413854328280921)
              ·
                refine ⟨14143947711310390746210691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18858596948413854328280921 14143947711310390746210691)
                ·
                  refine ⟨21215921566965586119316037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14143947711310390746210691 21215921566965586119316037)
                  ·
                    refine ⟨3977985293806047397371757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21215921566965586119316037 3977985293806047397371757)
                    ·
                      refine ⟨1491744485177267774014409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3977985293806047397371757 1491744485177267774014409)
                      ·
                        rfl

theorem cell23_2905162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_2905162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905162 prefixEnd_2905162 := by exact prefixLift 2905162
  have htrace : WordTrace (prefixWord ++ tailWord_2905162) baseStart_2905162 baseEnd_2905162 := by
    simpa [prefixWord, tailWord_2905162, baseEnd_2905162] using wordTrace_append hprefix tailTrace_2905162
  have hstable : (prefixWord ++ tailWord_2905162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905162).length < 2 ^ (prefixWord ++ tailWord_2905162).sum := by decide
  have hdescent : baseEnd_2905162 < baseStart_2905162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905212 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2905212 : Nat := 118140960795 + 2905212 * 2 ^ 59
def prefixEnd_2905212 : Nat := 4983230072969 + 3 ^ 40 * 2905212 * 2
def baseEnd_2905212 : Nat := 497256719736664192796393

theorem tailTrace_2905212 : CollatzResearch.WordTrace tailWord_2905212 prefixEnd_2905212 497256719736664192796393 := by
  unfold tailWord_2905212
  simp only [CollatzResearch.WordTrace]
  refine ⟨52980893375460284776270945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70641191167280379701694593 52980893375460284776270945)
  ·
    refine ⟨39735670031595213582203209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52980893375460284776270945 39735670031595213582203209)
    ·
      refine ⟨29801752523696410186652407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39735670031595213582203209 29801752523696410186652407)
      ·
        refine ⟨44702628785544615279978611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801752523696410186652407 44702628785544615279978611)
        ·
          refine ⟨67053943178316922919967917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44702628785544615279978611 67053943178316922919967917)
          ·
            refine ⟨25145228691868846094987969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67053943178316922919967917 25145228691868846094987969)
            ·
              refine ⟨18858921518901634571240977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25145228691868846094987969 18858921518901634571240977)
              ·
                refine ⟨14144191139176225928430733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18858921518901634571240977 14144191139176225928430733)
                ·
                  refine ⟨5304071677191084723161525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14144191139176225928430733 5304071677191084723161525)
                  ·
                    refine ⟨497256719736664192796393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5304071677191084723161525 497256719736664192796393)
                    ·
                      rfl

theorem cell23_2905212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2905212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905212 prefixEnd_2905212 := by exact prefixLift 2905212
  have htrace : WordTrace (prefixWord ++ tailWord_2905212) baseStart_2905212 baseEnd_2905212 := by
    simpa [prefixWord, tailWord_2905212, baseEnd_2905212] using wordTrace_append hprefix tailTrace_2905212
  have hstable : (prefixWord ++ tailWord_2905212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905212).length < 2 ^ (prefixWord ++ tailWord_2905212).sum := by decide
  have hdescent : baseEnd_2905212 < baseStart_2905212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905215 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_2905215 : Nat := 118140960795 + 2905215 * 2 ^ 59
def prefixEnd_2905215 : Nat := 4983230072969 + 3 ^ 40 * 2905215 * 2
def baseEnd_2905215 : Nat := 1491771699651956066651665

theorem tailTrace_2905215 : CollatzResearch.WordTrace tailWord_2905215 prefixEnd_2905215 1491771699651956066651665 := by
  unfold tailWord_2905215
  simp only [CollatzResearch.WordTrace]
  refine ⟨105961896169909701064901099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70641264113273134043267399 105961896169909701064901099)
  ·
    refine ⟨158942844254864551597351649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105961896169909701064901099 158942844254864551597351649)
    ·
      refine ⟨119207133191148413698013737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158942844254864551597351649 119207133191148413698013737)
      ·
        refine ⟨89405349893361310273510303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119207133191148413698013737 89405349893361310273510303)
        ·
          refine ⟨134108024840041965410265455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89405349893361310273510303 134108024840041965410265455)
          ·
            refine ⟨201162037260062948115398183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134108024840041965410265455 201162037260062948115398183)
            ·
              refine ⟨301743055890094422173097275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201162037260062948115398183 301743055890094422173097275)
              ·
                refine ⟨452614583835141633259645913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301743055890094422173097275 452614583835141633259645913)
                ·
                  refine ⟨339460937876356224944734435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452614583835141633259645913 339460937876356224944734435)
                  ·
                    refine ⟨509191406814534337417101653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339460937876356224944734435 509191406814534337417101653)
                    ·
                      refine ⟨1491771699651956066651665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 509191406814534337417101653 1491771699651956066651665)
                      ·
                        rfl

theorem cell23_2905215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_2905215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905215 prefixEnd_2905215 := by exact prefixLift 2905215
  have htrace : WordTrace (prefixWord ++ tailWord_2905215) baseStart_2905215 baseEnd_2905215 := by
    simpa [prefixWord, tailWord_2905215, baseEnd_2905215] using wordTrace_append hprefix tailTrace_2905215
  have hstable : (prefixWord ++ tailWord_2905215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905215).length < 2 ^ (prefixWord ++ tailWord_2905215).sum := by decide
  have hdescent : baseEnd_2905215 < baseStart_2905215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905219 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 4, 3, 2]
def baseStart_2905219 : Nat := 118140960795 + 2905219 * 2 ^ 59
def prefixEnd_2905219 : Nat := 4983230072969 + 3 ^ 40 * 2905219 * 2
def baseEnd_2905219 : Nat := 1491773753574574051001647

theorem tailTrace_2905219 : CollatzResearch.WordTrace tailWord_2905219 prefixEnd_2905219 1491773753574574051001647 := by
  unfold tailWord_2905219
  simp only [CollatzResearch.WordTrace]
  refine ⟨105962042061895209748046711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70641361374596806498697807 105962042061895209748046711)
  ·
    refine ⟨158943063092842814622070067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105962042061895209748046711 158943063092842814622070067)
    ·
      refine ⟨238414594639264221933105101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158943063092842814622070067 238414594639264221933105101)
      ·
        refine ⟨89405472989724083224914413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238414594639264221933105101 89405472989724083224914413)
        ·
          refine ⟨33527052371146531209342905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89405472989724083224914413 33527052371146531209342905)
          ·
            refine ⟨25145289278359898407007179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33527052371146531209342905 25145289278359898407007179)
            ·
              refine ⟨37717933917539847610510769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25145289278359898407007179 37717933917539847610510769)
              ·
                refine ⟨28288450438154885707883077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37717933917539847610510769 28288450438154885707883077)
                ·
                  refine ⟨5304084457154041070228077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28288450438154885707883077 5304084457154041070228077)
                  ·
                    refine ⟨1989031671432765401335529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5304084457154041070228077 1989031671432765401335529)
                    ·
                      refine ⟨1491773753574574051001647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989031671432765401335529 1491773753574574051001647)
                      ·
                        rfl

theorem cell23_2905219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_2905219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905219 prefixEnd_2905219 := by exact prefixLift 2905219
  have htrace : WordTrace (prefixWord ++ tailWord_2905219) baseStart_2905219 baseEnd_2905219 := by
    simpa [prefixWord, tailWord_2905219, baseEnd_2905219] using wordTrace_append hprefix tailTrace_2905219
  have hstable : (prefixWord ++ tailWord_2905219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905219).length < 2 ^ (prefixWord ++ tailWord_2905219).sum := by decide
  have hdescent : baseEnd_2905219 < baseStart_2905219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905276 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_2905276 : Nat := 118140960795 + 2905276 * 2 ^ 59
def prefixEnd_2905276 : Nat := 4983230072969 + 3 ^ 40 * 2905276 * 2
def baseEnd_2905276 : Nat := 497267673990626775996295

theorem tailTrace_2905276 : CollatzResearch.WordTrace tailWord_2905276 prefixEnd_2905276 497267673990626775996295 := by
  unfold tailWord_2905276
  simp only [CollatzResearch.WordTrace]
  refine ⟨52982060511344354241435841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70642747348459138988581121 52982060511344354241435841)
  ·
    refine ⟨39736545383508265681076881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52982060511344354241435841 39736545383508265681076881)
    ·
      refine ⟨29802409037631199260807661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39736545383508265681076881 29802409037631199260807661)
      ·
        refine ⟨11175903389111699722802873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29802409037631199260807661 11175903389111699722802873)
        ·
          refine ⟨8381927541833774792102155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175903389111699722802873 8381927541833774792102155)
          ·
            refine ⟨12572891312750662188153233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381927541833774792102155 12572891312750662188153233)
            ·
              refine ⟨9429668484562996641114925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12572891312750662188153233 9429668484562996641114925)
              ·
                refine ⟨3536125681711123740418097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9429668484562996641114925 3536125681711123740418097)
                ·
                  refine ⟨2652094261283342805313573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3536125681711123740418097 2652094261283342805313573)
                  ·
                    refine ⟨497267673990626775996295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652094261283342805313573 497267673990626775996295)
                    ·
                      rfl

theorem cell23_2905276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_2905276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905276 prefixEnd_2905276 := by exact prefixLift 2905276
  have htrace : WordTrace (prefixWord ++ tailWord_2905276) baseStart_2905276 baseEnd_2905276 := by
    simpa [prefixWord, tailWord_2905276, baseEnd_2905276] using wordTrace_append hprefix tailTrace_2905276
  have hstable : (prefixWord ++ tailWord_2905276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905276).length < 2 ^ (prefixWord ++ tailWord_2905276).sum := by decide
  have hdescent : baseEnd_2905276 < baseStart_2905276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905299 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 3]
def baseStart_2905299 : Nat := 118140960795 + 2905299 * 2 ^ 59
def prefixEnd_2905299 : Nat := 4983230072969 + 3 ^ 40 * 2905299 * 2
def baseEnd_2905299 : Nat := 1491814832026933738001279

theorem tailTrace_2905299 : CollatzResearch.WordTrace tailWord_2905299 prefixEnd_2905299 1491814832026933738001279 := by
  unfold tailWord_2905299
  simp only [CollatzResearch.WordTrace]
  refine ⟨105964959901605383410958951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70643306601070255607305967 105964959901605383410958951)
  ·
    refine ⟨158947439852408075116438427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105964959901605383410958951 158947439852408075116438427)
    ·
      refine ⟨238421159778612112674657641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158947439852408075116438427 238421159778612112674657641)
      ·
        refine ⟨178815869833959084505993231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238421159778612112674657641 178815869833959084505993231)
        ·
          refine ⟨268223804750938626758989847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178815869833959084505993231 268223804750938626758989847)
          ·
            refine ⟨402335707126407940138484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268223804750938626758989847 402335707126407940138484771)
            ·
              refine ⟨603503560689611910207727157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402335707126407940138484771 603503560689611910207727157)
              ·
                refine ⟨56578458814651116581974421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603503560689611910207727157 56578458814651116581974421)
                ·
                  refine ⟨2652115256936771089780051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56578458814651116581974421 2652115256936771089780051)
                  ·
                    refine ⟨3978172885405156634670077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652115256936771089780051 3978172885405156634670077)
                    ·
                      refine ⟨1491814832026933738001279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3978172885405156634670077 1491814832026933738001279)
                      ·
                        rfl

theorem cell23_2905299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_2905299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905299 prefixEnd_2905299 := by exact prefixLift 2905299
  have htrace : WordTrace (prefixWord ++ tailWord_2905299) baseStart_2905299 baseEnd_2905299 := by
    simpa [prefixWord, tailWord_2905299, baseEnd_2905299] using wordTrace_append hprefix tailTrace_2905299
  have hstable : (prefixWord ++ tailWord_2905299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905299).length < 2 ^ (prefixWord ++ tailWord_2905299).sum := by decide
  have hdescent : baseEnd_2905299 < baseStart_2905299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905326 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_2905326 : Nat := 118140960795 + 2905326 * 2 ^ 59
def prefixEnd_2905326 : Nat := 4983230072969 + 3 ^ 40 * 2905326 * 2
def baseEnd_2905326 : Nat := 1491828696004605132363655

theorem tailTrace_2905326 : CollatzResearch.WordTrace tailWord_2905326 prefixEnd_2905326 1491828696004605132363655 := by
  unfold tailWord_2905326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13245743084063445877773979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70643963115005044681461221 13245743084063445877773979)
  ·
    refine ⟨19868614626095168816660969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13245743084063445877773979 19868614626095168816660969)
    ·
      refine ⟨14901460969571376612495727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19868614626095168816660969 14901460969571376612495727)
      ·
        refine ⟨22352191454357064918743591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14901460969571376612495727 22352191454357064918743591)
        ·
          refine ⟨33528287181535597378115387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22352191454357064918743591 33528287181535597378115387)
          ·
            refine ⟨50292430772303396067173081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33528287181535597378115387 50292430772303396067173081)
            ·
              refine ⟨37719323079227547050379811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50292430772303396067173081 37719323079227547050379811)
              ·
                refine ⟨56578984618841320575569717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37719323079227547050379811 56578984618841320575569717)
                ·
                  refine ⟨5304279808016373803959661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56578984618841320575569717 5304279808016373803959661)
                  ·
                    refine ⟨1989104928006140176484873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5304279808016373803959661 1989104928006140176484873)
                    ·
                      refine ⟨1491828696004605132363655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989104928006140176484873 1491828696004605132363655)
                      ·
                        rfl

theorem cell23_2905326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_2905326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905326 prefixEnd_2905326 := by exact prefixLift 2905326
  have htrace : WordTrace (prefixWord ++ tailWord_2905326) baseStart_2905326 baseEnd_2905326 := by
    simpa [prefixWord, tailWord_2905326, baseEnd_2905326] using wordTrace_append hprefix tailTrace_2905326
  have hstable : (prefixWord ++ tailWord_2905326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905326).length < 2 ^ (prefixWord ++ tailWord_2905326).sum := by decide
  have hdescent : baseEnd_2905326 < baseStart_2905326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905343 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 1, 3, 2]
def baseStart_2905343 : Nat := 118140960795 + 2905343 * 2 ^ 59
def prefixEnd_2905343 : Nat := 4983230072969 + 3 ^ 40 * 2905343 * 2
def baseEnd_2905343 : Nat := 1491837425175731565851077

theorem tailTrace_2905343 : CollatzResearch.WordTrace tailWord_2905343 prefixEnd_2905343 1491837425175731565851077 := by
  unfold tailWord_2905343
  simp only [CollatzResearch.WordTrace]
  refine ⟨105966564713445978925560683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70644376475630652617040455 105966564713445978925560683)
  ·
    refine ⟨158949847070168968388341025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105966564713445978925560683 158949847070168968388341025)
    ·
      refine ⟨119212385302626726291255769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158949847070168968388341025 119212385302626726291255769)
      ·
        refine ⟨89409288976970044718441827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119212385302626726291255769 89409288976970044718441827)
        ·
          refine ⟨134113933465455067077662741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89409288976970044718441827 134113933465455067077662741)
          ·
            refine ⟨6286590631193206269265441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134113933465455067077662741 6286590631193206269265441)
            ·
              refine ⟨4714942973394904701949081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6286590631193206269265441 4714942973394904701949081)
              ·
                refine ⟨3536207230046178526461811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714942973394904701949081 3536207230046178526461811)
                ·
                  refine ⟨5304310845069267789692717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536207230046178526461811 5304310845069267789692717)
                  ·
                    refine ⟨1989116566900975421134769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5304310845069267789692717 1989116566900975421134769)
                    ·
                      refine ⟨1491837425175731565851077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989116566900975421134769 1491837425175731565851077)
                      ·
                        rfl

theorem cell23_2905343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_2905343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905343 prefixEnd_2905343 := by exact prefixLift 2905343
  have htrace : WordTrace (prefixWord ++ tailWord_2905343) baseStart_2905343 baseEnd_2905343 := by
    simpa [prefixWord, tailWord_2905343, baseEnd_2905343] using wordTrace_append hprefix tailTrace_2905343
  have hstable : (prefixWord ++ tailWord_2905343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905343).length < 2 ^ (prefixWord ++ tailWord_2905343).sum := by decide
  have hdescent : baseEnd_2905343 < baseStart_2905343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905379 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 7]
def baseStart_2905379 : Nat := 118140960795 + 2905379 * 2 ^ 59
def prefixEnd_2905379 : Nat := 4983230072969 + 3 ^ 40 * 2905379 * 2
def baseEnd_2905379 : Nat := 165761767831032602777879

theorem tailTrace_2905379 : CollatzResearch.WordTrace tailWord_2905379 prefixEnd_2905379 165761767831032602777879 := by
  unfold tailWord_2905379
  simp only [CollatzResearch.WordTrace]
  refine ⟨105967877741315557073871191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70645251827543704715914127 105967877741315557073871191)
  ·
    refine ⟨158951816611973335610806787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105967877741315557073871191 158951816611973335610806787)
    ·
      refine ⟨238427724917960003416210181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158951816611973335610806787 238427724917960003416210181)
      ·
        refine ⟨44705198422117500640539409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238427724917960003416210181 44705198422117500640539409)
        ·
          refine ⟨33528898816588125480404557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44705198422117500640539409 33528898816588125480404557)
          ·
            refine ⟨12573337056220547055151709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33528898816588125480404557 12573337056220547055151709)
            ·
              refine ⟨4715001396082705145681891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12573337056220547055151709 4715001396082705145681891)
              ·
                refine ⟨7072502094124057718522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715001396082705145681891 7072502094124057718522837)
                ·
                  refine ⟨165761767831032602777879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7072502094124057718522837 165761767831032602777879)
                  ·
                    rfl

theorem cell23_2905379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 7].length) (baseStart_2905379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905379 prefixEnd_2905379 := by exact prefixLift 2905379
  have htrace : WordTrace (prefixWord ++ tailWord_2905379) baseStart_2905379 baseEnd_2905379 := by
    simpa [prefixWord, tailWord_2905379, baseEnd_2905379] using wordTrace_append hprefix tailTrace_2905379
  have hstable : (prefixWord ++ tailWord_2905379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905379).length < 2 ^ (prefixWord ++ tailWord_2905379).sum := by decide
  have hdescent : baseEnd_2905379 < baseStart_2905379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905456 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_2905456 : Nat := 118140960795 + 2905456 * 2 ^ 59
def prefixEnd_2905456 : Nat := 4983230072969 + 3 ^ 40 * 2905456 * 2
def baseEnd_2905456 : Nat := 497298482829896541246019

theorem tailTrace_2905456 : CollatzResearch.WordTrace tailWord_2905456 prefixEnd_2905456 497298482829896541246019 := by
  unfold tailWord_2905456
  simp only [CollatzResearch.WordTrace]
  refine ⟨52985343081018299612212111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70647124108024399482949481 52985343081018299612212111)
  ·
    refine ⟨79478014621527449418318167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52985343081018299612212111 79478014621527449418318167)
    ·
      refine ⟨119217021932291174127477251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79478014621527449418318167 119217021932291174127477251)
      ·
        refine ⟨178825532898436761191215877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119217021932291174127477251 178825532898436761191215877)
        ·
          refine ⟨33529787418456892723352977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178825532898436761191215877 33529787418456892723352977)
          ·
            refine ⟨25147340563842669542514733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33529787418456892723352977 25147340563842669542514733)
            ·
              refine ⟨9430252711441001078443025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25147340563842669542514733 9430252711441001078443025)
              ·
                refine ⟨7072689533580750808832269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9430252711441001078443025 7072689533580750808832269)
                ·
                  refine ⟨2652258575092781553312101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7072689533580750808832269 2652258575092781553312101)
                  ·
                    refine ⟨497298482829896541246019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652258575092781553312101 497298482829896541246019)
                    ·
                      rfl

theorem cell23_2905456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_2905456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905456 prefixEnd_2905456 := by exact prefixLift 2905456
  have htrace : WordTrace (prefixWord ++ tailWord_2905456) baseStart_2905456 baseEnd_2905456 := by
    simpa [prefixWord, tailWord_2905456, baseEnd_2905456] using wordTrace_append hprefix tailTrace_2905456
  have hstable : (prefixWord ++ tailWord_2905456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905456).length < 2 ^ (prefixWord ++ tailWord_2905456).sum := by decide
  have hdescent : baseEnd_2905456 < baseStart_2905456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905469 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 8]
def baseStart_2905469 : Nat := 118140960795 + 2905469 * 2 ^ 59
def prefixEnd_2905469 : Nat := 4983230072969 + 3 ^ 40 * 2905469 * 2
def baseEnd_2905469 : Nat := 165766902637577563652833

theorem tailTrace_2905469 : CollatzResearch.WordTrace tailWord_2905469 prefixEnd_2905469 165766902637577563652833 := by
  unfold tailWord_2905469
  simp only [CollatzResearch.WordTrace]
  refine ⟨105971160310989502444647461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70647440207326334963098307 105971160310989502444647461)
  ·
    refine ⟨19869592558310531708371399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105971160310989502444647461 19869592558310531708371399)
    ·
      refine ⟨29804388837465797562557099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19869592558310531708371399 29804388837465797562557099)
      ·
        refine ⟨44706583256198696343835649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29804388837465797562557099 44706583256198696343835649)
        ·
          refine ⟨33529937442149022257876737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44706583256198696343835649 33529937442149022257876737)
          ·
            refine ⟨25147453081611766693407553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33529937442149022257876737 25147453081611766693407553)
            ·
              refine ⟨18860589811208825020055665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25147453081611766693407553 18860589811208825020055665)
              ·
                refine ⟨14145442358406618765041749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18860589811208825020055665 14145442358406618765041749)
                ·
                  refine ⟨165766902637577563652833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14145442358406618765041749 165766902637577563652833)
                  ·
                    rfl

theorem cell23_2905469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_2905469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905469 prefixEnd_2905469 := by exact prefixLift 2905469
  have htrace : WordTrace (prefixWord ++ tailWord_2905469) baseStart_2905469 baseEnd_2905469 := by
    simpa [prefixWord, tailWord_2905469, baseEnd_2905469] using wordTrace_append hprefix tailTrace_2905469
  have hstable : (prefixWord ++ tailWord_2905469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905469).length < 2 ^ (prefixWord ++ tailWord_2905469).sum := by decide
  have hdescent : baseEnd_2905469 < baseStart_2905469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905503 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 6]
def baseStart_2905503 : Nat := 118140960795 + 2905503 * 2 ^ 59
def prefixEnd_2905503 : Nat := 4983230072969 + 3 ^ 40 * 2905503 * 2
def baseEnd_2905503 : Nat := 165768842453383437761149

theorem tailTrace_2905503 : CollatzResearch.WordTrace tailWord_2905503 prefixEnd_2905503 165768842453383437761149 := by
  unfold tailWord_2905503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105972400392866326251385163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70648266928577550834256775 105972400392866326251385163)
  ·
    refine ⟨158958600589299489377077745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105972400392866326251385163 158958600589299489377077745)
    ·
      refine ⟨119218950441974617032808309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158958600589299489377077745 119218950441974617032808309)
      ·
        refine ⟨11176776603935120346825779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119218950441974617032808309 11176776603935120346825779)
        ·
          refine ⟨16765164905902680520238669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11176776603935120346825779 16765164905902680520238669)
          ·
            refine ⟨6286936839713505195089501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16765164905902680520238669 6286936839713505195089501)
            ·
              refine ⟨2357601314892564448158563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6286936839713505195089501 2357601314892564448158563)
              ·
                refine ⟨3536401972338846672237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357601314892564448158563 3536401972338846672237845)
                ·
                  refine ⟨165768842453383437761149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3536401972338846672237845 165768842453383437761149)
                  ·
                    rfl

theorem cell23_2905503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 6].length) (baseStart_2905503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905503 prefixEnd_2905503 := by exact prefixLift 2905503
  have htrace : WordTrace (prefixWord ++ tailWord_2905503) baseStart_2905503 baseEnd_2905503 := by
    simpa [prefixWord, tailWord_2905503, baseEnd_2905503] using wordTrace_append hprefix tailTrace_2905503
  have hstable : (prefixWord ++ tailWord_2905503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905503).length < 2 ^ (prefixWord ++ tailWord_2905503).sum := by decide
  have hdescent : baseEnd_2905503 < baseStart_2905503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905516 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_2905516 : Nat := 118140960795 + 2905516 * 2 ^ 59
def prefixEnd_2905516 : Nat := 4983230072969 + 3 ^ 40 * 2905516 * 2
def baseEnd_2905516 : Nat := 497308752442986462995927

theorem tailTrace_2905516 : CollatzResearch.WordTrace tailWord_2905516 prefixEnd_2905516 497308752442986462995927 := by
  unfold tailWord_2905516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52986437270909614735804201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70648583027879486314405601 52986437270909614735804201)
  ·
    refine ⟨39739827953182211051853151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52986437270909614735804201 39739827953182211051853151)
    ·
      refine ⟨59609741929773316577779727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39739827953182211051853151 59609741929773316577779727)
      ·
        refine ⟨89414612894659974866669591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59609741929773316577779727 89414612894659974866669591)
        ·
          refine ⟨134121919341989962300004387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89414612894659974866669591 134121919341989962300004387)
          ·
            refine ⟨201182879012984943450006581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134121919341989962300004387 201182879012984943450006581)
            ·
              refine ⟨18860894907467338448438117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201182879012984943450006581 18860894907467338448438117)
              ·
                refine ⟨3536417795150125959082147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18860894907467338448438117 3536417795150125959082147)
                ·
                  refine ⟨5304626692725188938623221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536417795150125959082147 5304626692725188938623221)
                  ·
                    refine ⟨497308752442986462995927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5304626692725188938623221 497308752442986462995927)
                    ·
                      rfl

theorem cell23_2905516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_2905516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905516 prefixEnd_2905516 := by exact prefixLift 2905516
  have htrace : WordTrace (prefixWord ++ tailWord_2905516) baseStart_2905516 baseEnd_2905516 := by
    simpa [prefixWord, tailWord_2905516, baseEnd_2905516] using wordTrace_append hprefix tailTrace_2905516
  have hstable : (prefixWord ++ tailWord_2905516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905516).length < 2 ^ (prefixWord ++ tailWord_2905516).sum := by decide
  have hdescent : baseEnd_2905516 < baseStart_2905516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905519 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_2905519 : Nat := 118140960795 + 2905519 * 2 ^ 59
def prefixEnd_2905519 : Nat := 4983230072969 + 3 ^ 40 * 2905519 * 2
def baseEnd_2905519 : Nat := 1491927797770922877250267

theorem tailTrace_2905519 : CollatzResearch.WordTrace tailWord_2905519 prefixEnd_2905519 1491927797770922877250267 := by
  unfold tailWord_2905519
  simp only [CollatzResearch.WordTrace]
  refine ⟨105972983960808360983967611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70648655973872240655978407 105972983960808360983967611)
  ·
    refine ⟨158959475941212541475951417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105972983960808360983967611 158959475941212541475951417)
    ·
      refine ⟨119219606955909406106963563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158959475941212541475951417 119219606955909406106963563)
      ·
        refine ⟨178829410433864109160445345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119219606955909406106963563 178829410433864109160445345)
        ·
          refine ⟨134122057825398081870334009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178829410433864109160445345 134122057825398081870334009)
          ·
            refine ⟨100591543369048561402750507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134122057825398081870334009 100591543369048561402750507)
            ·
              refine ⟨150887315053572842104125761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100591543369048561402750507 150887315053572842104125761)
              ·
                refine ⟨113165486290179631578094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150887315053572842104125761 113165486290179631578094321)
                ·
                  refine ⟨84874114717634723683570741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113165486290179631578094321 84874114717634723683570741)
                  ·
                    refine ⟨7956948254778255345334757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84874114717634723683570741 7956948254778255345334757)
                    ·
                      refine ⟨1491927797770922877250267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7956948254778255345334757 1491927797770922877250267)
                      ·
                        rfl

theorem cell23_2905519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_2905519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905519 prefixEnd_2905519 := by exact prefixLift 2905519
  have htrace : WordTrace (prefixWord ++ tailWord_2905519) baseStart_2905519 baseEnd_2905519 := by
    simpa [prefixWord, tailWord_2905519, baseEnd_2905519] using wordTrace_append hprefix tailTrace_2905519
  have hstable : (prefixWord ++ tailWord_2905519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905519).length < 2 ^ (prefixWord ++ tailWord_2905519).sum := by decide
  have hdescent : baseEnd_2905519 < baseStart_2905519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905540 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2905540 : Nat := 118140960795 + 2905540 * 2 ^ 59
def prefixEnd_2905540 : Nat := 4983230072969 + 3 ^ 40 * 2905540 * 2
def baseEnd_2905540 : Nat := 1491938580864667295087671

theorem tailTrace_2905540 : CollatzResearch.WordTrace tailWord_2905540 prefixEnd_2905540 1491938580864667295087671 := by
  unfold tailWord_2905540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52986874946866140785241037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70649166595821521046988049 52986874946866140785241037)
  ·
    refine ⟨19870078105074802794465389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52986874946866140785241037 19870078105074802794465389)
    ·
      refine ⟨7451279289403051047924521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19870078105074802794465389 7451279289403051047924521)
      ·
        refine ⟨5588459467052288285943391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7451279289403051047924521 5588459467052288285943391)
        ·
          refine ⟨8382689200578432428915087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588459467052288285943391 8382689200578432428915087)
          ·
            refine ⟨12574033800867648643372631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382689200578432428915087 12574033800867648643372631)
            ·
              refine ⟨18861050701301472965058947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12574033800867648643372631 18861050701301472965058947)
              ·
                refine ⟨28291576051952209447588421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18861050701301472965058947 28291576051952209447588421)
                ·
                  refine ⟨5304670509741039271422829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28291576051952209447588421 5304670509741039271422829)
                  ·
                    refine ⟨1989251441152889726783561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5304670509741039271422829 1989251441152889726783561)
                    ·
                      refine ⟨1491938580864667295087671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989251441152889726783561 1491938580864667295087671)
                      ·
                        rfl

theorem cell23_2905540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2905540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905540 prefixEnd_2905540 := by exact prefixLift 2905540
  have htrace : WordTrace (prefixWord ++ tailWord_2905540) baseStart_2905540 baseEnd_2905540 := by
    simpa [prefixWord, tailWord_2905540, baseEnd_2905540] using wordTrace_append hprefix tailTrace_2905540
  have hstable : (prefixWord ++ tailWord_2905540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905540).length < 2 ^ (prefixWord ++ tailWord_2905540).sum := by decide
  have hdescent : baseEnd_2905540 < baseStart_2905540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905590 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2905590 : Nat := 118140960795 + 2905590 * 2 ^ 59
def prefixEnd_2905590 : Nat := 4983230072969 + 3 ^ 40 * 2905590 * 2
def baseEnd_2905590 : Nat := 1491964254897392099462441

theorem tailTrace_2905590 : CollatzResearch.WordTrace tailWord_2905590 prefixEnd_2905590 1491964254897392099462441 := by
  unfold tailWord_2905590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623473346471946256862639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70650382362367426739868149 6623473346471946256862639)
  ·
    refine ⟨9935210019707919385293959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623473346471946256862639 9935210019707919385293959)
    ·
      refine ⟨14902815029561879077940939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935210019707919385293959 14902815029561879077940939)
      ·
        refine ⟨22354222544342818616911409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902815029561879077940939 22354222544342818616911409)
        ·
          refine ⟨16765666908257113962683557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22354222544342818616911409 16765666908257113962683557)
          ·
            refine ⟨3143562545298208868003167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16765666908257113962683557 3143562545298208868003167)
            ·
              refine ⟨4715343817947313302004751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143562545298208868003167 4715343817947313302004751)
              ·
                refine ⟨7073015726920969953007127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715343817947313302004751 7073015726920969953007127)
                ·
                  refine ⟨10609523590381454929510691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073015726920969953007127 10609523590381454929510691)
                  ·
                    refine ⟨15914285385572182394266037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10609523590381454929510691 15914285385572182394266037)
                    ·
                      refine ⟨1491964254897392099462441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15914285385572182394266037 1491964254897392099462441)
                      ·
                        rfl

theorem cell23_2905590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2905590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905590 prefixEnd_2905590 := by exact prefixLift 2905590
  have htrace : WordTrace (prefixWord ++ tailWord_2905590) baseStart_2905590 baseEnd_2905590 := by
    simpa [prefixWord, tailWord_2905590, baseEnd_2905590] using wordTrace_append hprefix tailTrace_2905590
  have hstable : (prefixWord ++ tailWord_2905590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905590).length < 2 ^ (prefixWord ++ tailWord_2905590).sum := by decide
  have hdescent : baseEnd_2905590 < baseStart_2905590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905598 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2905598 : Nat := 118140960795 + 2905598 * 2 ^ 59
def prefixEnd_2905598 : Nat := 4983230072969 + 3 ^ 40 * 2905598 * 2
def baseEnd_2905598 : Nat := 1491968362742628068162405

theorem tailTrace_2905598 : CollatzResearch.WordTrace tailWord_2905598 prefixEnd_2905598 1491968362742628068162405 := by
  unfold tailWord_2905598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246983165940269684511681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70650576885014771650728965 13246983165940269684511681)
  ·
    refine ⟨9935237374455202263383761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13246983165940269684511681 9935237374455202263383761)
    ·
      refine ⟨7451428030841401697537821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9935237374455202263383761 7451428030841401697537821)
      ·
        refine ⟨2794285511565525636576683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7451428030841401697537821 2794285511565525636576683)
        ·
          refine ⟨4191428267348288454865025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794285511565525636576683 4191428267348288454865025)
          ·
            refine ⟨3143571200511216341148769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191428267348288454865025 3143571200511216341148769)
            ·
              refine ⟨2357678400383412255861577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143571200511216341148769 2357678400383412255861577)
              ·
                refine ⟨1768258800287559191896183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357678400383412255861577 1768258800287559191896183)
                ·
                  refine ⟨2652388200431338787844275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768258800287559191896183 2652388200431338787844275)
                  ·
                    refine ⟨3978582300647008181766413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652388200431338787844275 3978582300647008181766413)
                    ·
                      refine ⟨1491968362742628068162405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3978582300647008181766413 1491968362742628068162405)
                      ·
                        rfl

theorem cell23_2905598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2905598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905598 prefixEnd_2905598 := by exact prefixLift 2905598
  have htrace : WordTrace (prefixWord ++ tailWord_2905598) baseStart_2905598 baseEnd_2905598 := by
    simpa [prefixWord, tailWord_2905598, baseEnd_2905598] using wordTrace_append hprefix tailTrace_2905598
  have hstable : (prefixWord ++ tailWord_2905598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905598).length < 2 ^ (prefixWord ++ tailWord_2905598).sum := by decide
  have hdescent : baseEnd_2905598 < baseStart_2905598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905626 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2905626 : Nat := 118140960795 + 2905626 * 2 ^ 59
def prefixEnd_2905626 : Nat := 4983230072969 + 3 ^ 40 * 2905626 * 2
def baseEnd_2905626 : Nat := 1491982740200953958612275

theorem tailTrace_2905626 : CollatzResearch.WordTrace tailWord_2905626 prefixEnd_2905626 1491982740200953958612275 := by
  unfold tailWord_2905626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494221642855179564528183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70651257714280478838741821 26494221642855179564528183)
  ·
    refine ⟨39741332464282769346792275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26494221642855179564528183 39741332464282769346792275)
    ·
      refine ⟨59611998696424154020188413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39741332464282769346792275 59611998696424154020188413)
      ·
        refine ⟨22354499511159057757570655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59611998696424154020188413 22354499511159057757570655)
        ·
          refine ⟨33531749266738586636355983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22354499511159057757570655 33531749266738586636355983)
          ·
            refine ⟨50297623900107879954533975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33531749266738586636355983 50297623900107879954533975)
            ·
              refine ⟨75446435850161819931800963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50297623900107879954533975 75446435850161819931800963)
              ·
                refine ⟨113169653775242729897701445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75446435850161819931800963 113169653775242729897701445)
                ·
                  refine ⟨21219310082858011855819021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113169653775242729897701445 21219310082858011855819021)
                  ·
                    refine ⟨7957241281071754445932133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21219310082858011855819021 7957241281071754445932133)
                    ·
                      refine ⟨1491982740200953958612275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7957241281071754445932133 1491982740200953958612275)
                      ·
                        rfl

theorem cell23_2905626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2905626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905626 prefixEnd_2905626 := by exact prefixLift 2905626
  have htrace : WordTrace (prefixWord ++ tailWord_2905626) baseStart_2905626 baseEnd_2905626 := by
    simpa [prefixWord, tailWord_2905626, baseEnd_2905626] using wordTrace_append hprefix tailTrace_2905626
  have hstable : (prefixWord ++ tailWord_2905626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905626).length < 2 ^ (prefixWord ++ tailWord_2905626).sum := by decide
  have hdescent : baseEnd_2905626 < baseStart_2905626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905700 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2905700 : Nat := 118140960795 + 2905700 * 2 ^ 59
def prefixEnd_2905700 : Nat := 4983230072969 + 3 ^ 40 * 2905700 * 2
def baseEnd_2905700 : Nat := 165780081974376296565215

theorem tailTrace_2905700 : CollatzResearch.WordTrace tailWord_2905700 prefixEnd_2905700 165780081974376296565215 := by
  unfold tailWord_2905700
  simp only [CollatzResearch.WordTrace]
  refine ⟨52989792786576314448153277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70653057048768419264204369 52989792786576314448153277)
  ·
    refine ⟨19871172294966117918057479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52989792786576314448153277 19871172294966117918057479)
    ·
      refine ⟨29806758442449176877086219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19871172294966117918057479 29806758442449176877086219)
      ·
        refine ⟨44710137663673765315629329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29806758442449176877086219 44710137663673765315629329)
        ·
          refine ⟨33532603247755323986721997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44710137663673765315629329 33532603247755323986721997)
          ·
            refine ⟨12574726217908246495020749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33532603247755323986721997 12574726217908246495020749)
            ·
              refine ⟨4715522331715592435632781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12574726217908246495020749 4715522331715592435632781)
              ·
                refine ⟨1768320874393347163362293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4715522331715592435632781 1768320874393347163362293)
                ·
                  refine ⟨165780081974376296565215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768320874393347163362293 165780081974376296565215)
                  ·
                    rfl

theorem cell23_2905700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2905700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905700 prefixEnd_2905700 := by exact prefixLift 2905700
  have htrace : WordTrace (prefixWord ++ tailWord_2905700) baseStart_2905700 baseEnd_2905700 := by
    simpa [prefixWord, tailWord_2905700, baseEnd_2905700] using wordTrace_append hprefix tailTrace_2905700
  have hstable : (prefixWord ++ tailWord_2905700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905700).length < 2 ^ (prefixWord ++ tailWord_2905700).sum := by decide
  have hdescent : baseEnd_2905700 < baseStart_2905700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905733 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2905733 : Nat := 118140960795 + 2905733 * 2 ^ 59
def prefixEnd_2905733 : Nat := 4983230072969 + 3 ^ 40 * 2905733 * 2
def baseEnd_2905733 : Nat := 1492037682630985039974283

theorem tailTrace_2905733 : CollatzResearch.WordTrace tailWord_2905733 prefixEnd_2905733 1492037682630985039974283 := by
  unfold tailWord_2905733
  simp only [CollatzResearch.WordTrace]
  refine ⟨105980789182033075532257853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70653859454688717021505235 105980789182033075532257853)
  ·
    refine ⟨39742795943262403324596695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105980789182033075532257853 39742795943262403324596695)
    ·
      refine ⟨59614193914893604986895043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39742795943262403324596695 59614193914893604986895043)
      ·
        refine ⟨89421290872340407480342565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59614193914893604986895043 89421290872340407480342565)
        ·
          refine ⟨16766492038563826402564231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89421290872340407480342565 16766492038563826402564231)
          ·
            refine ⟨25149738057845739603846347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16766492038563826402564231 25149738057845739603846347)
            ·
              refine ⟨37724607086768609405769521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25149738057845739603846347 37724607086768609405769521)
              ·
                refine ⟨28293455315076457054327141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37724607086768609405769521 28293455315076457054327141)
                ·
                  refine ⟨5305022871576835697686339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28293455315076457054327141 5305022871576835697686339)
                  ·
                    refine ⟨7957534307365253546529509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5305022871576835697686339 7957534307365253546529509)
                    ·
                      refine ⟨1492037682630985039974283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7957534307365253546529509 1492037682630985039974283)
                      ·
                        rfl

theorem cell23_2905733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2905733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905733 prefixEnd_2905733 := by exact prefixLift 2905733
  have htrace : WordTrace (prefixWord ++ tailWord_2905733) baseStart_2905733 baseEnd_2905733 := by
    simpa [prefixWord, tailWord_2905733, baseEnd_2905733] using wordTrace_append hprefix tailTrace_2905733
  have hstable : (prefixWord ++ tailWord_2905733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905733).length < 2 ^ (prefixWord ++ tailWord_2905733).sum := by decide
  have hdescent : baseEnd_2905733 < baseStart_2905733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905768 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 5]
def baseStart_2905768 : Nat := 118140960795 + 2905768 * 2 ^ 59
def prefixEnd_2905768 : Nat := 4983230072969 + 3 ^ 40 * 2905768 * 2
def baseEnd_2905768 : Nat := 165783961605988044781847

theorem tailTrace_2905768 : CollatzResearch.WordTrace tailWord_2905768 prefixEnd_2905768 165783961605988044781847 := by
  unfold tailWord_2905768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52991032868453138254890979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70654710491270851006521305 52991032868453138254890979)
  ·
    refine ⟨79486549302679707382336469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52991032868453138254890979 79486549302679707382336469)
    ·
      refine ⟨1862965999281555641773511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 79486549302679707382336469 1862965999281555641773511)
      ·
        refine ⟨2794448998922333462660267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862965999281555641773511 2794448998922333462660267)
        ·
          refine ⟨4191673498383500193990401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794448998922333462660267 4191673498383500193990401)
          ·
            refine ⟨3143755123787625145492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191673498383500193990401 3143755123787625145492801)
            ·
              refine ⟨2357816342840718859119601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143755123787625145492801 2357816342840718859119601)
              ·
                refine ⟨1768362257130539144339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357816342840718859119601 1768362257130539144339701)
                ·
                  refine ⟨165783961605988044781847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768362257130539144339701 165783961605988044781847)
                  ·
                    rfl

theorem cell23_2905768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 5].length) (baseStart_2905768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905768 prefixEnd_2905768 := by exact prefixLift 2905768
  have htrace : WordTrace (prefixWord ++ tailWord_2905768) baseStart_2905768 baseEnd_2905768 := by
    simpa [prefixWord, tailWord_2905768, baseEnd_2905768] using wordTrace_append hprefix tailTrace_2905768
  have hstable : (prefixWord ++ tailWord_2905768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905768).length < 2 ^ (prefixWord ++ tailWord_2905768).sum := by decide
  have hdescent : baseEnd_2905768 < baseStart_2905768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905790 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2905790 : Nat := 118140960795 + 2905790 * 2 ^ 59
def prefixEnd_2905790 : Nat := 4983230072969 + 3 ^ 40 * 2905790 * 2
def baseEnd_2905790 : Nat := 165785216780921257440169

theorem tailTrace_2905790 : CollatzResearch.WordTrace tailWord_2905790 prefixEnd_2905790 165785216780921257440169 := by
  unfold tailWord_2905790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247858517853321783385353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70655245428551049511388549 13247858517853321783385353)
  ·
    refine ⟨9935893888389991337539015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13247858517853321783385353 9935893888389991337539015)
    ·
      refine ⟨14903840832584987006308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935893888389991337539015 14903840832584987006308523)
      ·
        refine ⟨22355761248877480509462785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14903840832584987006308523 22355761248877480509462785)
        ·
          refine ⟨16766820936658110382097089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22355761248877480509462785 16766820936658110382097089)
          ·
            refine ⟨12575115702493582786572817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16766820936658110382097089 12575115702493582786572817)
            ·
              refine ⟨9431336776870187089929613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12575115702493582786572817 9431336776870187089929613)
              ·
                refine ⟨3536751291326320158723605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9431336776870187089929613 3536751291326320158723605)
                ·
                  refine ⟨165785216780921257440169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3536751291326320158723605 165785216780921257440169)
                  ·
                    rfl

theorem cell23_2905790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2905790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905790 prefixEnd_2905790 := by exact prefixLift 2905790
  have htrace : WordTrace (prefixWord ++ tailWord_2905790) baseStart_2905790 baseEnd_2905790 := by
    simpa [prefixWord, tailWord_2905790, baseEnd_2905790] using wordTrace_append hprefix tailTrace_2905790
  have hstable : (prefixWord ++ tailWord_2905790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905790).length < 2 ^ (prefixWord ++ tailWord_2905790).sum := by decide
  have hdescent : baseEnd_2905790 < baseStart_2905790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905804 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2905804 : Nat := 118140960795 + 2905804 * 2 ^ 59
def prefixEnd_2905804 : Nat := 4983230072969 + 3 ^ 40 * 2905804 * 2
def baseEnd_2905804 : Nat := 1492074139757454262186457

theorem tailTrace_2905804 : CollatzResearch.WordTrace tailWord_2905804 prefixEnd_2905804 1492074139757454262186457 := by
  unfold tailWord_2905804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52991689382387927329046233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70655585843183903105394977 52991689382387927329046233)
  ·
    refine ⟨39743767036790945496784675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52991689382387927329046233 39743767036790945496784675)
    ·
      refine ⟨59615650555186418245177013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39743767036790945496784675 59615650555186418245177013)
      ·
        refine ⟨5588967239548726710485345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59615650555186418245177013 5588967239548726710485345)
        ·
          refine ⟨4191725429661545032864009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5588967239548726710485345 4191725429661545032864009)
          ·
            refine ⟨3143794072246158774648007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191725429661545032864009 3143794072246158774648007)
            ·
              refine ⟨4715691108369238161972011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143794072246158774648007 4715691108369238161972011)
              ·
                refine ⟨7073536662553857242958017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715691108369238161972011 7073536662553857242958017)
                ·
                  refine ⟨5305152496915392932218513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7073536662553857242958017 5305152496915392932218513)
                  ·
                    refine ⟨3978864372686544699163885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305152496915392932218513 3978864372686544699163885)
                    ·
                      refine ⟨1492074139757454262186457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3978864372686544699163885 1492074139757454262186457)
                      ·
                        rfl

theorem cell23_2905804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2905804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905804 prefixEnd_2905804 := by exact prefixLift 2905804
  have htrace : WordTrace (prefixWord ++ tailWord_2905804) baseStart_2905804 baseEnd_2905804 := by
    simpa [prefixWord, tailWord_2905804, baseEnd_2905804] using wordTrace_append hprefix tailTrace_2905804
  have hstable : (prefixWord ++ tailWord_2905804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905804).length < 2 ^ (prefixWord ++ tailWord_2905804).sum := by decide
  have hdescent : baseEnd_2905804 < baseStart_2905804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905834 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_2905834 : Nat := 118140960795 + 2905834 * 2 ^ 59
def prefixEnd_2905834 : Nat := 4983230072969 + 3 ^ 40 * 2905834 * 2
def baseEnd_2905834 : Nat := 1492089544177089144811319

theorem tailTrace_2905834 : CollatzResearch.WordTrace tailWord_2905834 prefixEnd_2905834 1492089544177089144811319 := by
  unfold tailWord_2905834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496118238666792445421139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70656315303111446521123037 26496118238666792445421139)
  ·
    refine ⟨39744177358000188668131709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26496118238666792445421139 39744177358000188668131709)
    ·
      refine ⟨14904066509250070750549391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39744177358000188668131709 14904066509250070750549391)
      ·
        refine ⟨22356099763875106125824087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14904066509250070750549391 22356099763875106125824087)
        ·
          refine ⟨33534149645812659188736131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22356099763875106125824087 33534149645812659188736131)
          ·
            refine ⟨50301224468718988783104197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33534149645812659188736131 50301224468718988783104197)
            ·
              refine ⟨9431479587884810396832037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50301224468718988783104197 9431479587884810396832037)
              ·
                refine ⟨1768402422728401949406007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9431479587884810396832037 1768402422728401949406007)
                ·
                  refine ⟨2652603634092602924109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768402422728401949406007 2652603634092602924109011)
                  ·
                    refine ⟨3978905451138904386163517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652603634092602924109011 3978905451138904386163517)
                    ·
                      refine ⟨1492089544177089144811319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3978905451138904386163517 1492089544177089144811319)
                      ·
                        rfl

theorem cell23_2905834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_2905834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905834 prefixEnd_2905834 := by exact prefixLift 2905834
  have htrace : WordTrace (prefixWord ++ tailWord_2905834) baseStart_2905834 baseEnd_2905834 := by
    simpa [prefixWord, tailWord_2905834, baseEnd_2905834] using wordTrace_append hprefix tailTrace_2905834
  have hstable : (prefixWord ++ tailWord_2905834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905834).length < 2 ^ (prefixWord ++ tailWord_2905834).sum := by decide
  have hdescent : baseEnd_2905834 < baseStart_2905834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905843 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_2905843 : Nat := 118140960795 + 2905843 * 2 ^ 59
def prefixEnd_2905843 : Nat := 4983230072969 + 3 ^ 40 * 2905843 * 2
def baseEnd_2905843 : Nat := 1492094165502979609598777

theorem tailTrace_2905843 : CollatzResearch.WordTrace tailWord_2905843 prefixEnd_2905843 1492094165502979609598777 := by
  unfold tailWord_2905843
  simp only [CollatzResearch.WordTrace]
  refine ⟨105984801211634564318762183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70656534141089709545841455 105984801211634564318762183)
  ·
    refine ⟨158977201817451846478143275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105984801211634564318762183 158977201817451846478143275)
    ·
      refine ⟨238465802726177769717214913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158977201817451846478143275 238465802726177769717214913)
      ·
        refine ⟨178849352044633327287911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238465802726177769717214913 178849352044633327287911185)
        ·
          refine ⟨134137014033474995465933389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178849352044633327287911185 134137014033474995465933389)
          ·
            refine ⟨50301380262553123299725021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134137014033474995465933389 50301380262553123299725021)
            ·
              refine ⟨18863017598457421237396883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50301380262553123299725021 18863017598457421237396883)
              ·
                refine ⟨28294526397686131856095325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18863017598457421237396883 28294526397686131856095325)
                ·
                  refine ⟨10610447399132299446035747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28294526397686131856095325 10610447399132299446035747)
                  ·
                    refine ⟨15915671098698449169053621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10610447399132299446035747 15915671098698449169053621)
                    ·
                      refine ⟨1492094165502979609598777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15915671098698449169053621 1492094165502979609598777)
                      ·
                        rfl

theorem cell23_2905843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_2905843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905843 prefixEnd_2905843 := by exact prefixLift 2905843
  have htrace : WordTrace (prefixWord ++ tailWord_2905843) baseStart_2905843 baseEnd_2905843 := by
    simpa [prefixWord, tailWord_2905843, baseEnd_2905843] using wordTrace_append hprefix tailTrace_2905843
  have hstable : (prefixWord ++ tailWord_2905843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905843).length < 2 ^ (prefixWord ++ tailWord_2905843).sum := by decide
  have hdescent : baseEnd_2905843 < baseStart_2905843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905854 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2905854 : Nat := 118140960795 + 2905854 * 2 ^ 59
def prefixEnd_2905854 : Nat := 4983230072969 + 3 ^ 40 * 2905854 * 2
def baseEnd_2905854 : Nat := 497366604596726355520409

theorem tailTrace_2905854 : CollatzResearch.WordTrace tailWord_2905854 prefixEnd_2905854 497366604596726355520409 := by
  unfold tailWord_2905854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248150301824339149676577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70656801609729808798275077 13248150301824339149676577)
  ·
    refine ⟨9936112726368254362257433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13248150301824339149676577 9936112726368254362257433)
    ·
      refine ⟨7452084544776190771693075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9936112726368254362257433 7452084544776190771693075)
      ·
        refine ⟨11178126817164286157539613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452084544776190771693075 11178126817164286157539613)
        ·
          refine ⟨4191797556436607309077355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11178126817164286157539613 4191797556436607309077355)
          ·
            refine ⟨6287696334654910963616033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191797556436607309077355 6287696334654910963616033)
            ·
              refine ⟨4715772250991183222712025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6287696334654910963616033 4715772250991183222712025)
              ·
                refine ⟨3536829188243387417034019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715772250991183222712025 3536829188243387417034019)
                ·
                  refine ⟨5305243782365081125551029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536829188243387417034019 5305243782365081125551029)
                  ·
                    refine ⟨497366604596726355520409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5305243782365081125551029 497366604596726355520409)
                    ·
                      rfl

theorem cell23_2905854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2905854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905854 prefixEnd_2905854 := by exact prefixLift 2905854
  have htrace : WordTrace (prefixWord ++ tailWord_2905854) baseStart_2905854 baseEnd_2905854 := by
    simpa [prefixWord, tailWord_2905854, baseEnd_2905854] using wordTrace_append hprefix tailTrace_2905854
  have hstable : (prefixWord ++ tailWord_2905854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905854).length < 2 ^ (prefixWord ++ tailWord_2905854).sum := by decide
  have hdescent : baseEnd_2905854 < baseStart_2905854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905870 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2905870 : Nat := 118140960795 + 2905870 * 2 ^ 59
def prefixEnd_2905870 : Nat := 4983230072969 + 3 ^ 40 * 2905870 * 2
def baseEnd_2905870 : Nat := 1492108029480651003961153

theorem tailTrace_2905870 : CollatzResearch.WordTrace tailWord_2905870 prefixEnd_2905870 1492108029480651003961153 := by
  unfold tailWord_2905870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248223247817093491249383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70657190655024498619996709 13248223247817093491249383)
  ·
    refine ⟨19872334871725640236874075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13248223247817093491249383 19872334871725640236874075)
    ·
      refine ⟨29808502307588460355311113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19872334871725640236874075 29808502307588460355311113)
      ·
        refine ⟨22356376730691345266483335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29808502307588460355311113 22356376730691345266483335)
        ·
          refine ⟨33534565096037017899725003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22356376730691345266483335 33534565096037017899725003)
          ·
            refine ⟨50301847644055526849587505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33534565096037017899725003 50301847644055526849587505)
            ·
              refine ⟨37726385733041645137190629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50301847644055526849587505 37726385733041645137190629)
              ·
                refine ⟨7073697324945308463223243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37726385733041645137190629 7073697324945308463223243)
                ·
                  refine ⟨10610545987417962694834865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073697324945308463223243 10610545987417962694834865)
                  ·
                    refine ⟨7957909490563472021126149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10610545987417962694834865 7957909490563472021126149)
                    ·
                      refine ⟨1492108029480651003961153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7957909490563472021126149 1492108029480651003961153)
                      ·
                        rfl

theorem cell23_2905870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2905870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905870 prefixEnd_2905870 := by exact prefixLift 2905870
  have htrace : WordTrace (prefixWord ++ tailWord_2905870) baseStart_2905870 baseEnd_2905870 := by
    simpa [prefixWord, tailWord_2905870, baseEnd_2905870] using wordTrace_append hprefix tailTrace_2905870
  have hstable : (prefixWord ++ tailWord_2905870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905870).length < 2 ^ (prefixWord ++ tailWord_2905870).sum := by decide
  have hdescent : baseEnd_2905870 < baseStart_2905870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905874 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2905874 : Nat := 118140960795 + 2905874 * 2 ^ 59
def prefixEnd_2905874 : Nat := 4983230072969 + 3 ^ 40 * 2905874 * 2
def baseEnd_2905874 : Nat := 1492110083403268988311135

theorem tailTrace_2905874 : CollatzResearch.WordTrace tailWord_2905874 prefixEnd_2905874 1492110083403268988311135 := by
  unfold tailWord_2905874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496482968630564153285169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70657287916348171075427117 26496482968630564153285169)
  ·
    refine ⟨19872362226472923114963877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26496482968630564153285169 19872362226472923114963877)
    ·
      refine ⟨3726067917463673084055727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19872362226472923114963877 3726067917463673084055727)
      ·
        refine ⟨5589101876195509626083591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726067917463673084055727 5589101876195509626083591)
        ·
          refine ⟨8383652814293264439125387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589101876195509626083591 8383652814293264439125387)
          ·
            refine ⟨12575479221439896658688081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8383652814293264439125387 12575479221439896658688081)
            ·
              refine ⟨9431609416079922494016061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12575479221439896658688081 9431609416079922494016061)
              ·
                refine ⟨3536853531029970935256023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9431609416079922494016061 3536853531029970935256023)
                ·
                  refine ⟨5305280296544956402884035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536853531029970935256023 5305280296544956402884035)
                  ·
                    refine ⟨7957920444817434604326053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5305280296544956402884035 7957920444817434604326053)
                    ·
                      refine ⟨1492110083403268988311135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7957920444817434604326053 1492110083403268988311135)
                      ·
                        rfl

theorem cell23_2905874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2905874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905874 prefixEnd_2905874 := by exact prefixLift 2905874
  have htrace : WordTrace (prefixWord ++ tailWord_2905874) baseStart_2905874 baseEnd_2905874 := by
    simpa [prefixWord, tailWord_2905874, baseEnd_2905874] using wordTrace_append hprefix tailTrace_2905874
  have hstable : (prefixWord ++ tailWord_2905874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905874).length < 2 ^ (prefixWord ++ tailWord_2905874).sum := by decide
  have hdescent : baseEnd_2905874 < baseStart_2905874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905877 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2905877 : Nat := 118140960795 + 2905877 * 2 ^ 59
def prefixEnd_2905877 : Nat := 4983230072969 + 3 ^ 40 * 2905877 * 2
def baseEnd_2905877 : Nat := 1492111623845232476573621

theorem tailTrace_2905877 : CollatzResearch.WordTrace tailWord_2905877 prefixEnd_2905877 1492111623845232476573621 := by
  unfold tailWord_2905877
  simp only [CollatzResearch.WordTrace]
  refine ⟨105986041293511388125499885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70657360862340925416999923 105986041293511388125499885)
  ·
    refine ⟨39744765485066770547062457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105986041293511388125499885 39744765485066770547062457)
    ·
      refine ⟨29808574113800077910296843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39744765485066770547062457 29808574113800077910296843)
      ·
        refine ⟨44712861170700116865445265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29808574113800077910296843 44712861170700116865445265)
        ·
          refine ⟨33534645878025087649083949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44712861170700116865445265 33534645878025087649083949)
          ·
            refine ⟨12575492204259407868406481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33534645878025087649083949 12575492204259407868406481)
            ·
              refine ⟨9431619153194555901304861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12575492204259407868406481 9431619153194555901304861)
              ·
                refine ⟨3536857182447958462989323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9431619153194555901304861 3536857182447958462989323)
                ·
                  refine ⟨5305285773671937694483985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536857182447958462989323 5305285773671937694483985)
                  ·
                    refine ⟨3978964330253953270862989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305285773671937694483985 3978964330253953270862989)
                    ·
                      refine ⟨1492111623845232476573621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3978964330253953270862989 1492111623845232476573621)
                      ·
                        rfl

theorem cell23_2905877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2905877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905877 prefixEnd_2905877 := by exact prefixLift 2905877
  have htrace : WordTrace (prefixWord ++ tailWord_2905877) baseStart_2905877 baseEnd_2905877 := by
    simpa [prefixWord, tailWord_2905877, baseEnd_2905877] using wordTrace_append hprefix tailTrace_2905877
  have hstable : (prefixWord ++ tailWord_2905877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905877).length < 2 ^ (prefixWord ++ tailWord_2905877).sum := by decide
  have hdescent : baseEnd_2905877 < baseStart_2905877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905903 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_2905903 : Nat := 118140960795 + 2905903 * 2 ^ 59
def prefixEnd_2905903 : Nat := 4983230072969 + 3 ^ 40 * 2905903 * 2
def baseEnd_2905903 : Nat := 1492124974342249374848501

theorem tailTrace_2905903 : CollatzResearch.WordTrace tailWord_2905903 prefixEnd_2905903 1492124974342249374848501 := by
  unfold tailWord_2905903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105986989591417194565946363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70657993060944796377297575 105986989591417194565946363)
  ·
    refine ⟨158980484387125791848919545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105986989591417194565946363 158980484387125791848919545)
    ·
      refine ⟨119235363290344343886689659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158980484387125791848919545 119235363290344343886689659)
      ·
        refine ⟨178853044935516515830034489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119235363290344343886689659 178853044935516515830034489)
        ·
          refine ⟨134139783701637386872525867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178853044935516515830034489 134139783701637386872525867)
          ·
            refine ⟨201209675552456080308788801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134139783701637386872525867 201209675552456080308788801)
            ·
              refine ⟨150907256664342060231591601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201209675552456080308788801 150907256664342060231591601)
              ·
                refine ⟨113180442498256545173693701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150907256664342060231591601 113180442498256545173693701)
                ·
                  refine ⟨21221332968423102220067569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113180442498256545173693701 21221332968423102220067569)
                  ·
                    refine ⟨15915999726317326665050677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21221332968423102220067569 15915999726317326665050677)
                    ·
                      refine ⟨1492124974342249374848501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15915999726317326665050677 1492124974342249374848501)
                      ·
                        rfl

theorem cell23_2905903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_2905903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905903 prefixEnd_2905903 := by exact prefixLift 2905903
  have htrace : WordTrace (prefixWord ++ tailWord_2905903) baseStart_2905903 baseEnd_2905903 := by
    simpa [prefixWord, tailWord_2905903, baseEnd_2905903] using wordTrace_append hprefix tailTrace_2905903
  have hstable : (prefixWord ++ tailWord_2905903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905903).length < 2 ^ (prefixWord ++ tailWord_2905903).sum := by decide
  have hdescent : baseEnd_2905903 < baseStart_2905903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905964 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_2905964 : Nat := 118140960795 + 2905964 * 2 ^ 59
def prefixEnd_2905964 : Nat := 4983230072969 + 3 ^ 40 * 2905964 * 2
def baseEnd_2905964 : Nat := 1492156296662173636185721

theorem tailTrace_2905964 : CollatzResearch.WordTrace tailWord_2905964 prefixEnd_2905964 1492156296662173636185721 := by
  unfold tailWord_2905964
  simp only [CollatzResearch.WordTrace]
  refine ⟨52994607222098100991958473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70659476296130801322611297 52994607222098100991958473)
  ·
    refine ⟨39745955416573575743968855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52994607222098100991958473 39745955416573575743968855)
    ·
      refine ⟨59618933124860363615953283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39745955416573575743968855 59618933124860363615953283)
      ·
        refine ⟨89428399687290545423929925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59618933124860363615953283 89428399687290545423929925)
        ·
          refine ⟨16767824941366977266986861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89428399687290545423929925 16767824941366977266986861)
          ·
            refine ⟨6287934353012616475120073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16767824941366977266986861 6287934353012616475120073)
            ·
              refine ⟨4715950764759462356340055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6287934353012616475120073 4715950764759462356340055)
              ·
                refine ⟨7073926147139193534510083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715950764759462356340055 7073926147139193534510083)
                ·
                  refine ⟨10610889220708790301765125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073926147139193534510083 10610889220708790301765125)
                  ·
                    refine ⟨1989541728882898181580961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10610889220708790301765125 1989541728882898181580961)
                    ·
                      refine ⟨1492156296662173636185721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989541728882898181580961 1492156296662173636185721)
                      ·
                        rfl

theorem cell23_2905964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_2905964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905964 prefixEnd_2905964 := by exact prefixLift 2905964
  have htrace : WordTrace (prefixWord ++ tailWord_2905964) baseStart_2905964 baseEnd_2905964 := by
    simpa [prefixWord, tailWord_2905964, baseEnd_2905964] using wordTrace_append hprefix tailTrace_2905964
  have hstable : (prefixWord ++ tailWord_2905964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905964).length < 2 ^ (prefixWord ++ tailWord_2905964).sum := by decide
  have hdescent : baseEnd_2905964 < baseStart_2905964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905985 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2905985 : Nat := 118140960795 + 2905985 * 2 ^ 59
def prefixEnd_2905985 : Nat := 4983230072969 + 3 ^ 40 * 2905985 * 2
def baseEnd_2905985 : Nat := 1492167079755918054023125

theorem tailTrace_2905985 : CollatzResearch.WordTrace tailWord_2905985 prefixEnd_2905985 1492167079755918054023125 := by
  unfold tailWord_2905985
  simp only [CollatzResearch.WordTrace]
  refine ⟨105989980377120122570431409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70659986918080081713620939 105989980377120122570431409)
  ·
    refine ⟨79492485282840091927823557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105989980377120122570431409 79492485282840091927823557)
    ·
      refine ⟨14904840990532517236466917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79492485282840091927823557 14904840990532517236466917)
      ·
        refine ⟨2794657685724846981837547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14904840990532517236466917 2794657685724846981837547)
        ·
          refine ⟨4191986528587270472756321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794657685724846981837547 4191986528587270472756321)
          ·
            refine ⟨3143989896440452854567241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191986528587270472756321 3143989896440452854567241)
            ·
              refine ⟨2357992422330339640925431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143989896440452854567241 2357992422330339640925431)
              ·
                refine ⟨3536988633495509461388147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357992422330339640925431 3536988633495509461388147)
                ·
                  refine ⟨5305482950243264192082221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536988633495509461388147 5305482950243264192082221)
                  ·
                    refine ⟨1989556106341224072030833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5305482950243264192082221 1989556106341224072030833)
                    ·
                      refine ⟨1492167079755918054023125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989556106341224072030833 1492167079755918054023125)
                      ·
                        rfl

theorem cell23_2905985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2905985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905985 prefixEnd_2905985 := by exact prefixLift 2905985
  have htrace : WordTrace (prefixWord ++ tailWord_2905985) baseStart_2905985 baseEnd_2905985 := by
    simpa [prefixWord, tailWord_2905985, baseEnd_2905985] using wordTrace_append hprefix tailTrace_2905985
  have hstable : (prefixWord ++ tailWord_2905985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905985).length < 2 ^ (prefixWord ++ tailWord_2905985).sum := by decide
  have hdescent : baseEnd_2905985 < baseStart_2905985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905987 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 5]
def baseStart_2905987 : Nat := 118140960795 + 2905987 * 2 ^ 59
def prefixEnd_2905987 : Nat := 4983230072969 + 3 ^ 40 * 2905987 * 2
def baseEnd_2905987 : Nat := 165796456301914116244235

theorem tailTrace_2905987 : CollatzResearch.WordTrace tailWord_2905987 prefixEnd_2905987 165796456301914116244235 := by
  unfold tailWord_2905987
  simp only [CollatzResearch.WordTrace]
  refine ⟨105990053323112876912004215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70660035548741917941336143 105990053323112876912004215)
  ·
    refine ⟨158985079984669315368006323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105990053323112876912004215 158985079984669315368006323)
    ·
      refine ⟨238477619977003973052009485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158985079984669315368006323 238477619977003973052009485)
      ·
        refine ⟨89429107491376489894503557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238477619977003973052009485 89429107491376489894503557)
        ·
          refine ⟨16767957654633091855219417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89429107491376489894503557 16767957654633091855219417)
          ·
            refine ⟨12575968240974818891414563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16767957654633091855219417 12575968240974818891414563)
            ·
              refine ⟨18863952361462228337121845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12575968240974818891414563 18863952361462228337121845)
              ·
                refine ⟨1768495533887083906605173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18863952361462228337121845 1768495533887083906605173)
                ·
                  refine ⟨165796456301914116244235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768495533887083906605173 165796456301914116244235)
                  ·
                    rfl

theorem cell23_2905987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 5].length) (baseStart_2905987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905987 prefixEnd_2905987 := by exact prefixLift 2905987
  have htrace : WordTrace (prefixWord ++ tailWord_2905987) baseStart_2905987 baseEnd_2905987 := by
    simpa [prefixWord, tailWord_2905987, baseEnd_2905987] using wordTrace_append hprefix tailTrace_2905987
  have hstable : (prefixWord ++ tailWord_2905987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905987).length < 2 ^ (prefixWord ++ tailWord_2905987).sum := by decide
  have hdescent : baseEnd_2905987 < baseStart_2905987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2905998 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2905998 : Nat := 118140960795 + 2905998 * 2 ^ 59
def prefixEnd_2905998 : Nat := 4983230072969 + 3 ^ 40 * 2905998 * 2
def baseEnd_2905998 : Nat := 1492173755004426503160565

theorem tailTrace_2905998 : CollatzResearch.WordTrace tailWord_2905998 prefixEnd_2905998 1492173755004426503160565 := by
  unfold tailWord_2905998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248806815759128223831831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70660303017382017193769765 13248806815759128223831831)
  ·
    refine ⟨19873210223638692335747747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13248806815759128223831831 19873210223638692335747747)
    ·
      refine ⟨29809815335458038503621621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19873210223638692335747747 29809815335458038503621621)
      ·
        refine ⟨2794670187699191109714527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29809815335458038503621621 2794670187699191109714527)
        ·
          refine ⟨4192005281548786664571791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794670187699191109714527 4192005281548786664571791)
          ·
            refine ⟨6288007922323179996857687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192005281548786664571791 6288007922323179996857687)
            ·
              refine ⟨9432011883484769995286531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288007922323179996857687 9432011883484769995286531)
              ·
                refine ⟨14148017825227154992929797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9432011883484769995286531 14148017825227154992929797)
                ·
                  refine ⟨2652753342230091561174337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14148017825227154992929797 2652753342230091561174337)
                  ·
                    refine ⟨1989565006672568670880753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2652753342230091561174337 1989565006672568670880753)
                    ·
                      refine ⟨1492173755004426503160565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989565006672568670880753 1492173755004426503160565)
                      ·
                        rfl

theorem cell23_2905998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2905998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2905998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2905998 prefixEnd_2905998 := by exact prefixLift 2905998
  have htrace : WordTrace (prefixWord ++ tailWord_2905998) baseStart_2905998 baseEnd_2905998 := by
    simpa [prefixWord, tailWord_2905998, baseEnd_2905998] using wordTrace_append hprefix tailTrace_2905998
  have hstable : (prefixWord ++ tailWord_2905998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2905998).length < 2 ^ (prefixWord ++ tailWord_2905998).sum := by decide
  have hdescent : baseEnd_2905998 < baseStart_2905998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2905998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906004 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 5]
def baseStart_2906004 : Nat := 118140960795 + 2906004 * 2 ^ 59
def prefixEnd_2906004 : Nat := 4983230072969 + 3 ^ 40 * 2906004 * 2
def baseEnd_2906004 : Nat := 165797426209817053298393

theorem tailTrace_2906004 : CollatzResearch.WordTrace tailWord_2906004 prefixEnd_2906004 165797426209817053298393 := by
  unfold tailWord_2906004
  simp only [CollatzResearch.WordTrace]
  refine ⟨52995336682025644407686533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70660448909367525876915377 52995336682025644407686533)
  ·
    refine ⟨9936625627879808326441225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52995336682025644407686533 9936625627879808326441225)
    ·
      refine ⟨7452469220909856244830919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9936625627879808326441225 7452469220909856244830919)
      ·
        refine ⟨11178703831364784367246379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452469220909856244830919 11178703831364784367246379)
        ·
          refine ⟨16768055747047176550869569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11178703831364784367246379 16768055747047176550869569)
          ·
            refine ⟨12576041810285382413152177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16768055747047176550869569 12576041810285382413152177)
            ·
              refine ⟨9432031357714036809864133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12576041810285382413152177 9432031357714036809864133)
              ·
                refine ⟨1768505879571381901849525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9432031357714036809864133 1768505879571381901849525)
                ·
                  refine ⟨165797426209817053298393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1768505879571381901849525 165797426209817053298393)
                  ·
                    rfl

theorem cell23_2906004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_2906004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906004 prefixEnd_2906004 := by exact prefixLift 2906004
  have htrace : WordTrace (prefixWord ++ tailWord_2906004) baseStart_2906004 baseEnd_2906004 := by
    simpa [prefixWord, tailWord_2906004, baseEnd_2906004] using wordTrace_append hprefix tailTrace_2906004
  have hstable : (prefixWord ++ tailWord_2906004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906004).length < 2 ^ (prefixWord ++ tailWord_2906004).sum := by decide
  have hdescent : baseEnd_2906004 < baseStart_2906004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906037 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2906037 : Nat := 118140960795 + 2906037 * 2 ^ 59
def prefixEnd_2906037 : Nat := 4983230072969 + 3 ^ 40 * 2906037 * 2
def baseEnd_2906037 : Nat := 1492193780749951850572885

theorem tailTrace_2906037 : CollatzResearch.WordTrace tailWord_2906037 prefixEnd_2906037 1492193780749951850572885 := by
  unfold tailWord_2906037
  simp only [CollatzResearch.WordTrace]
  refine ⟨105991876972931735451324365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70661251315287823634216243 105991876972931735451324365)
  ·
    refine ⟨39746953864849400794246637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105991876972931735451324365 39746953864849400794246637)
    ·
      refine ⟨14905107699318525297842489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39746953864849400794246637 14905107699318525297842489)
      ·
        refine ⟨11178830774488893973381867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14905107699318525297842489 11178830774488893973381867)
        ·
          refine ⟨16768246161733340960072801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11178830774488893973381867 16768246161733340960072801)
          ·
            refine ⟨12576184621300005720054601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16768246161733340960072801 12576184621300005720054601)
            ·
              refine ⟨9432138465975004290040951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12576184621300005720054601 9432138465975004290040951)
              ·
                refine ⟨14148207698962506435061427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9432138465975004290040951 14148207698962506435061427)
                ·
                  refine ⟨21222311548443759652592141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14148207698962506435061427 21222311548443759652592141)
                  ·
                    refine ⟨7958366830666409869722053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21222311548443759652592141 7958366830666409869722053)
                    ·
                      refine ⟨1492193780749951850572885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7958366830666409869722053 1492193780749951850572885)
                      ·
                        rfl

theorem cell23_2906037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2906037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906037 prefixEnd_2906037 := by exact prefixLift 2906037
  have htrace : WordTrace (prefixWord ++ tailWord_2906037) baseStart_2906037 baseEnd_2906037 := by
    simpa [prefixWord, tailWord_2906037, baseEnd_2906037] using wordTrace_append hprefix tailTrace_2906037
  have hstable : (prefixWord ++ tailWord_2906037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906037).length < 2 ^ (prefixWord ++ tailWord_2906037).sum := by decide
  have hdescent : baseEnd_2906037 < baseStart_2906037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906057 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_2906057 : Nat := 118140960795 + 2906057 * 2 ^ 59
def prefixEnd_2906057 : Nat := 4983230072969 + 3 ^ 40 * 2906057 * 2
def baseEnd_2906057 : Nat := 1492204050363041772322793

theorem tailTrace_2906057 : CollatzResearch.WordTrace tailWord_2906057 prefixEnd_2906057 1492204050363041772322793 := by
  unfold tailWord_2906057
  simp only [CollatzResearch.WordTrace]
  refine ⟨105992606432859278867052425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70661737621906185911368283 105992606432859278867052425)
  ·
    refine ⟨79494454824644459150289319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105992606432859278867052425 79494454824644459150289319)
    ·
      refine ⟨119241682236966688725433979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79494454824644459150289319 119241682236966688725433979)
      ·
        refine ⟨178862523355450033088150969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119241682236966688725433979 178862523355450033088150969)
        ·
          refine ⟨134146892516587524816113227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178862523355450033088150969 134146892516587524816113227)
          ·
            refine ⟨201220338774881287224169841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134146892516587524816113227 201220338774881287224169841)
            ·
              refine ⟨150915254081160965418127381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201220338774881287224169841 150915254081160965418127381)
              ·
                refine ⟨7074152535054420253974721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150915254081160965418127381 7074152535054420253974721)
                ·
                  refine ⟨5305614401290815190481041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7074152535054420253974721 5305614401290815190481041)
                  ·
                    refine ⟨3979210800968111392860781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305614401290815190481041 3979210800968111392860781)
                    ·
                      refine ⟨1492204050363041772322793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3979210800968111392860781 1492204050363041772322793)
                      ·
                        rfl

theorem cell23_2906057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_2906057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906057 prefixEnd_2906057 := by exact prefixLift 2906057
  have htrace : WordTrace (prefixWord ++ tailWord_2906057) baseStart_2906057 baseEnd_2906057 := by
    simpa [prefixWord, tailWord_2906057, baseEnd_2906057] using wordTrace_append hprefix tailTrace_2906057
  have hstable : (prefixWord ++ tailWord_2906057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906057).length < 2 ^ (prefixWord ++ tailWord_2906057).sum := by decide
  have hdescent : baseEnd_2906057 < baseStart_2906057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906064 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 1, 4]
def baseStart_2906064 : Nat := 118140960795 + 2906064 * 2 ^ 59
def prefixEnd_2906064 : Nat := 4983230072969 + 3 ^ 40 * 2906064 * 2
def baseEnd_2906064 : Nat := 497402548242541081645087

theorem tailTrace_2906064 : CollatzResearch.WordTrace tailWord_2906064 prefixEnd_2906064 497402548242541081645087 := by
  unfold tailWord_2906064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52996430871916959531278623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70661907829222612708371497 52996430871916959531278623)
  ·
    refine ⟨79494646307875439296917935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52996430871916959531278623 79494646307875439296917935)
    ·
      refine ⟨119241969461813158945376903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79494646307875439296917935 119241969461813158945376903)
      ·
        refine ⟨178862954192719738418065355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119241969461813158945376903 178862954192719738418065355)
        ·
          refine ⟨268294431289079607627098033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178862954192719738418065355 268294431289079607627098033)
          ·
            refine ⟨201220823466809705720323525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268294431289079607627098033 201220823466809705720323525)
            ·
              refine ⟨37728904400026819822560661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201220823466809705720323525 37728904400026819822560661)
              ·
                refine ⟨1768542393751257179182531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37728904400026819822560661 1768542393751257179182531)
                ·
                  refine ⟨2652813590626885768773797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768542393751257179182531 2652813590626885768773797)
                  ·
                    refine ⟨497402548242541081645087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652813590626885768773797 497402548242541081645087)
                    ·
                      rfl

theorem cell23_2906064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_2906064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906064 prefixEnd_2906064 := by exact prefixLift 2906064
  have htrace : WordTrace (prefixWord ++ tailWord_2906064) baseStart_2906064 baseEnd_2906064 := by
    simpa [prefixWord, tailWord_2906064, baseEnd_2906064] using wordTrace_append hprefix tailTrace_2906064
  have hstable : (prefixWord ++ tailWord_2906064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906064).length < 2 ^ (prefixWord ++ tailWord_2906064).sum := by decide
  have hdescent : baseEnd_2906064 < baseStart_2906064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906080 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2906080 : Nat := 118140960795 + 2906080 * 2 ^ 59
def prefixEnd_2906080 : Nat := 4983230072969 + 3 ^ 40 * 2906080 * 2
def baseEnd_2906080 : Nat := 1492215860418095182335187

theorem tailTrace_2906080 : CollatzResearch.WordTrace tailWord_2906080 prefixEnd_2906080 1492215860418095182335187 := by
  unfold tailWord_2906080
  simp only [CollatzResearch.WordTrace]
  refine ⟨52996722655887976897569847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70662296874517302530093129 52996722655887976897569847)
  ·
    refine ⟨79495083983831965346354771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52996722655887976897569847 79495083983831965346354771)
    ·
      refine ⟨119242625975747948019532157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79495083983831965346354771 119242625975747948019532157)
      ·
        refine ⟨44715984740905480507324559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119242625975747948019532157 44715984740905480507324559)
        ·
          refine ⟨67073977111358220760986839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44715984740905480507324559 67073977111358220760986839)
          ·
            refine ⟨100610965667037331141480259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67073977111358220760986839 100610965667037331141480259)
            ·
              refine ⟨150916448500555996712220389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100610965667037331141480259 150916448500555996712220389)
              ·
                refine ⟨28296834093854249383541323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150916448500555996712220389 28296834093854249383541323)
                ·
                  refine ⟨42445251140781374075311985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28296834093854249383541323 42445251140781374075311985)
                  ·
                    refine ⟨31833938355586030556483989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42445251140781374075311985 31833938355586030556483989)
                    ·
                      refine ⟨1492215860418095182335187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31833938355586030556483989 1492215860418095182335187)
                      ·
                        rfl

theorem cell23_2906080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2906080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906080 prefixEnd_2906080 := by exact prefixLift 2906080
  have htrace : WordTrace (prefixWord ++ tailWord_2906080) baseStart_2906080 baseEnd_2906080 := by
    simpa [prefixWord, tailWord_2906080, baseEnd_2906080] using wordTrace_append hprefix tailTrace_2906080
  have hstable : (prefixWord ++ tailWord_2906080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906080).length < 2 ^ (prefixWord ++ tailWord_2906080).sum := by decide
  have hdescent : baseEnd_2906080 < baseStart_2906080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906107 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 1, 5]
def baseStart_2906107 : Nat := 118140960795 + 2906107 * 2 ^ 59
def prefixEnd_2906107 : Nat := 4983230072969 + 3 ^ 40 * 2906107 * 2
def baseEnd_2906107 : Nat := 497409908131922192232521

theorem tailTrace_2906107 : CollatzResearch.WordTrace tailWord_2906107 prefixEnd_2906107 497409908131922192232521 := by
  unfold tailWord_2906107
  simp only [CollatzResearch.WordTrace]
  refine ⟨105994430082678137406372575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70662953388452091604248383 105994430082678137406372575)
  ·
    refine ⟨158991645124017206109558863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105994430082678137406372575 158991645124017206109558863)
    ·
      refine ⟨238487467686025809164338295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158991645124017206109558863 238487467686025809164338295)
      ·
        refine ⟨357731201529038713746507443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238487467686025809164338295 357731201529038713746507443)
        ·
          refine ⟨536596802293558070619761165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357731201529038713746507443 536596802293558070619761165)
          ·
            refine ⟨201223800860084276482410437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536596802293558070619761165 201223800860084276482410437)
            ·
              refine ⟨37729462661265801840451957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201223800860084276482410437 37729462661265801840451957)
              ·
                refine ⟨3537137124493668922542371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37729462661265801840451957 3537137124493668922542371)
                ·
                  refine ⟨5305705686740503383813557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537137124493668922542371 5305705686740503383813557)
                  ·
                    refine ⟨497409908131922192232521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5305705686740503383813557 497409908131922192232521)
                    ·
                      rfl

theorem cell23_2906107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 5].length) (baseStart_2906107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906107 prefixEnd_2906107 := by exact prefixLift 2906107
  have htrace : WordTrace (prefixWord ++ tailWord_2906107) baseStart_2906107 baseEnd_2906107 := by
    simpa [prefixWord, tailWord_2906107, baseEnd_2906107] using wordTrace_append hprefix tailTrace_2906107
  have hstable : (prefixWord ++ tailWord_2906107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906107).length < 2 ^ (prefixWord ++ tailWord_2906107).sum := by decide
  have hdescent : baseEnd_2906107 < baseStart_2906107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906137 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_2906137 : Nat := 118140960795 + 2906137 * 2 ^ 59
def prefixEnd_2906137 : Nat := 4983230072969 + 3 ^ 40 * 2906137 * 2
def baseEnd_2906137 : Nat := 497415042938467153107475

theorem tailTrace_2906137 : CollatzResearch.WordTrace tailWord_2906137 prefixEnd_2906137 497415042938467153107475 := by
  unfold tailWord_2906137
  simp only [CollatzResearch.WordTrace]
  refine ⟨105995524272569452529964665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70663682848379635019976443 105995524272569452529964665)
  ·
    refine ⟨79496643204427089397473499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105995524272569452529964665 79496643204427089397473499)
    ·
      refine ⟨119244964806640634096210249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79496643204427089397473499 119244964806640634096210249)
      ·
        refine ⟨89433723604980475572157687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119244964806640634096210249 89433723604980475572157687)
        ·
          refine ⟨134150585407470713358236531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89433723604980475572157687 134150585407470713358236531)
          ·
            refine ⟨201225878111206070037354797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134150585407470713358236531 201225878111206070037354797)
            ·
              refine ⟨75459704291702276264008049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201225878111206070037354797 75459704291702276264008049)
              ·
                refine ⟨56594778218776707198006037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75459704291702276264008049 56594778218776707198006037)
                ·
                  refine ⟨2652880229005158149906533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56594778218776707198006037 2652880229005158149906533)
                  ·
                    refine ⟨497415042938467153107475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2652880229005158149906533 497415042938467153107475)
                    ·
                      rfl

theorem cell23_2906137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_2906137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906137 prefixEnd_2906137 := by exact prefixLift 2906137
  have htrace : WordTrace (prefixWord ++ tailWord_2906137) baseStart_2906137 baseEnd_2906137 := by
    simpa [prefixWord, tailWord_2906137, baseEnd_2906137] using wordTrace_append hprefix tailTrace_2906137
  have hstable : (prefixWord ++ tailWord_2906137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906137).length < 2 ^ (prefixWord ++ tailWord_2906137).sum := by decide
  have hdescent : baseEnd_2906137 < baseStart_2906137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906154 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2906154 : Nat := 118140960795 + 2906154 * 2 ^ 59
def prefixEnd_2906154 : Nat := 4983230072969 + 3 ^ 40 * 2906154 * 2
def baseEnd_2906154 : Nat := 497417952662175964269949

theorem tailTrace_2906154 : CollatzResearch.WordTrace tailWord_2906154 prefixEnd_2906154 497417952662175964269949 := by
  unfold tailWord_2906154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499036078376966108333379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70664096209005242955555677 26499036078376966108333379)
  ·
    refine ⟨39748554117565449162500069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26499036078376966108333379 39748554117565449162500069)
    ·
      refine ⟨7452853897043521717968763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39748554117565449162500069 7452853897043521717968763)
      ·
        refine ⟨11179280845565282576953145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452853897043521717968763 11179280845565282576953145)
        ·
          refine ⟨8384460634173961932714859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11179280845565282576953145 8384460634173961932714859)
          ·
            refine ⟨12576690951260942899072289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384460634173961932714859 12576690951260942899072289)
            ·
              refine ⟨9432518213445707174304217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12576690951260942899072289 9432518213445707174304217)
              ·
                refine ⟨7074388660084280380728163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9432518213445707174304217 7074388660084280380728163)
                ·
                  refine ⟨10611582990126420571092245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7074388660084280380728163 10611582990126420571092245)
                  ·
                    refine ⟨497417952662175964269949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10611582990126420571092245 497417952662175964269949)
                    ·
                      rfl

theorem cell23_2906154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2906154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906154 prefixEnd_2906154 := by exact prefixLift 2906154
  have htrace : WordTrace (prefixWord ++ tailWord_2906154) baseStart_2906154 baseEnd_2906154 := by
    simpa [prefixWord, tailWord_2906154, baseEnd_2906154] using wordTrace_append hprefix tailTrace_2906154
  have hstable : (prefixWord ++ tailWord_2906154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906154).length < 2 ^ (prefixWord ++ tailWord_2906154).sum := by decide
  have hdescent : baseEnd_2906154 < baseStart_2906154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906158 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2906158 : Nat := 118140960795 + 2906158 * 2 ^ 59
def prefixEnd_2906158 : Nat := 4983230072969 + 3 ^ 40 * 2906158 * 2
def baseEnd_2906158 : Nat := 497418637303048625719943

theorem tailTrace_2906158 : CollatzResearch.WordTrace tailWord_2906158 prefixEnd_2906158 497418637303048625719943 := by
  unfold tailWord_2906158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249536275686671639559891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70664193470328915410986085 13249536275686671639559891)
  ·
    refine ⟨19874304413530007459339837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13249536275686671639559891 19874304413530007459339837)
    ·
      refine ⟨7452864155073752797252439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19874304413530007459339837 7452864155073752797252439)
      ·
        refine ⟨11179296232610629195878659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452864155073752797252439 11179296232610629195878659)
        ·
          refine ⟨16768944348915943793817989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11179296232610629195878659 16768944348915943793817989)
          ·
            refine ⟨3144177065421739461340873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16768944348915943793817989 3144177065421739461340873)
            ·
              refine ⟨2358132799066304596005655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144177065421739461340873 2358132799066304596005655)
              ·
                refine ⟨3537199198599456894008483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358132799066304596005655 3537199198599456894008483)
                ·
                  refine ⟨5305798797899185341012725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537199198599456894008483 5305798797899185341012725)
                  ·
                    refine ⟨497418637303048625719943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5305798797899185341012725 497418637303048625719943)
                    ·
                      rfl

theorem cell23_2906158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2906158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906158 prefixEnd_2906158 := by exact prefixLift 2906158
  have htrace : WordTrace (prefixWord ++ tailWord_2906158) baseStart_2906158 baseEnd_2906158 := by
    simpa [prefixWord, tailWord_2906158, baseEnd_2906158] using wordTrace_append hprefix tailTrace_2906158
  have hstable : (prefixWord ++ tailWord_2906158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906158).length < 2 ^ (prefixWord ++ tailWord_2906158).sum := by decide
  have hdescent : baseEnd_2906158 < baseStart_2906158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906161 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_2906161 : Nat := 118140960795 + 2906161 * 2 ^ 59
def prefixEnd_2906161 : Nat := 4983230072969 + 3 ^ 40 * 2906161 * 2
def baseEnd_2906161 : Nat := 1492257452351109365422315

theorem tailTrace_2906161 : CollatzResearch.WordTrace tailWord_2906161 prefixEnd_2906161 1492257452351109365422315 := by
  unfold tailWord_2906161
  simp only [CollatzResearch.WordTrace]
  refine ⟨105996399624482504628838337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70664266416321669752558891 105996399624482504628838337)
  ·
    refine ⟨79497299718361878471628753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105996399624482504628838337 79497299718361878471628753)
    ·
      refine ⟨59622974788771408853721565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79497299718361878471628753 59622974788771408853721565)
      ·
        refine ⟨22358615545789278320145587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59622974788771408853721565 22358615545789278320145587)
        ·
          refine ⟨33537923318683917480218381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22358615545789278320145587 33537923318683917480218381)
          ·
            refine ⟨12576721244506469055081893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33537923318683917480218381 12576721244506469055081893)
            ·
              refine ⟨2358135233344962947827855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12576721244506469055081893 2358135233344962947827855)
              ·
                refine ⟨3537202850017444421741783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358135233344962947827855 3537202850017444421741783)
                ·
                  refine ⟨5305804275026166632612675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537202850017444421741783 5305804275026166632612675)
                  ·
                    refine ⟨7958706412539249948919013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5305804275026166632612675 7958706412539249948919013)
                    ·
                      refine ⟨1492257452351109365422315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7958706412539249948919013 1492257452351109365422315)
                      ·
                        rfl

theorem cell23_2906161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_2906161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906161 prefixEnd_2906161 := by exact prefixLift 2906161
  have htrace : WordTrace (prefixWord ++ tailWord_2906161) baseStart_2906161 baseEnd_2906161 := by
    simpa [prefixWord, tailWord_2906161, baseEnd_2906161] using wordTrace_append hprefix tailTrace_2906161
  have hstable : (prefixWord ++ tailWord_2906161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906161).length < 2 ^ (prefixWord ++ tailWord_2906161).sum := by decide
  have hdescent : baseEnd_2906161 < baseStart_2906161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906206 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2906206 : Nat := 118140960795 + 2906206 * 2 ^ 59
def prefixEnd_2906206 : Nat := 4983230072969 + 3 ^ 40 * 2906206 * 2
def baseEnd_2906206 : Nat := 1492280558980561689359609

theorem tailTrace_2906206 : CollatzResearch.WordTrace tailWord_2906206 prefixEnd_2906206 1492280558980561689359609 := by
  unfold tailWord_2906206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249755113664934664278309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70665360606212984876150981 13249755113664934664278309)
  ·
    refine ⟨2484329083812175249552183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13249755113664934664278309 2484329083812175249552183)
    ·
      refine ⟨3726493625718262874328275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484329083812175249552183 3726493625718262874328275)
      ·
        refine ⟨5589740438577394311492413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726493625718262874328275 5589740438577394311492413)
        ·
          refine ⟨2096152664466522866809655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5589740438577394311492413 2096152664466522866809655)
          ·
            refine ⟨3144228996699784300214483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096152664466522866809655 3144228996699784300214483)
            ·
              refine ⟨4716343495049676450321725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144228996699784300214483 4716343495049676450321725)
              ·
                refine ⟨1768628810643628668870647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716343495049676450321725 1768628810643628668870647)
                ·
                  refine ⟨2652943215965443003305971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768628810643628668870647 2652943215965443003305971)
                  ·
                    refine ⟨3979414823948164504958957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652943215965443003305971 3979414823948164504958957)
                    ·
                      refine ⟨1492280558980561689359609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3979414823948164504958957 1492280558980561689359609)
                      ·
                        rfl

theorem cell23_2906206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2906206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906206 prefixEnd_2906206 := by exact prefixLift 2906206
  have htrace : WordTrace (prefixWord ++ tailWord_2906206) baseStart_2906206 baseEnd_2906206 := by
    simpa [prefixWord, tailWord_2906206, baseEnd_2906206] using wordTrace_append hprefix tailTrace_2906206
  have hstable : (prefixWord ++ tailWord_2906206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906206).length < 2 ^ (prefixWord ++ tailWord_2906206).sum := by decide
  have hdescent : baseEnd_2906206 < baseStart_2906206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906245 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_2906245 : Nat := 118140960795 + 2906245 * 2 ^ 59
def prefixEnd_2906245 : Nat := 4983230072969 + 3 ^ 40 * 2906245 * 2
def baseEnd_2906245 : Nat := 1492300584726087036771929

theorem tailTrace_2906245 : CollatzResearch.WordTrace tailWord_2906245 prefixEnd_2906245 1492300584726087036771929 := by
  unfold tailWord_2906245
  simp only [CollatzResearch.WordTrace]
  refine ⟨105999463356178186974896189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70666308904118791316597459 105999463356178186974896189)
  ·
    refine ⟨39749798758566820115586071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105999463356178186974896189 39749798758566820115586071)
    ·
      refine ⟨59624698137850230173379107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39749798758566820115586071 59624698137850230173379107)
      ·
        refine ⟨89437047206775345260068661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59624698137850230173379107 89437047206775345260068661)
        ·
          refine ⟨8384723175635188618131437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89437047206775345260068661 8384723175635188618131437)
          ·
            refine ⟨3144271190863195731799289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8384723175635188618131437 3144271190863195731799289)
            ·
              refine ⟨2358203393147396798849467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144271190863195731799289 2358203393147396798849467)
              ·
                refine ⟨3537305089721095198274201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358203393147396798849467 3537305089721095198274201)
                ·
                  refine ⟨2652978817290821398705651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3537305089721095198274201 2652978817290821398705651)
                  ·
                    refine ⟨3979468225936232098058477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652978817290821398705651 3979468225936232098058477)
                    ·
                      refine ⟨1492300584726087036771929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3979468225936232098058477 1492300584726087036771929)
                      ·
                        rfl

theorem cell23_2906245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_2906245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906245 prefixEnd_2906245 := by exact prefixLift 2906245
  have htrace : WordTrace (prefixWord ++ tailWord_2906245) baseStart_2906245 baseEnd_2906245 := by
    simpa [prefixWord, tailWord_2906245, baseEnd_2906245] using wordTrace_append hprefix tailTrace_2906245
  have hstable : (prefixWord ++ tailWord_2906245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906245).length < 2 ^ (prefixWord ++ tailWord_2906245).sum := by decide
  have hdescent : baseEnd_2906245 < baseStart_2906245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906285 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_2906285 : Nat := 118140960795 + 2906285 * 2 ^ 59
def prefixEnd_2906285 : Nat := 4983230072969 + 3 ^ 40 * 2906285 * 2
def baseEnd_2906285 : Nat := 1492321123952266880271745

theorem tailTrace_2906285 : CollatzResearch.WordTrace tailWord_2906285 prefixEnd_2906285 1492321123952266880271745 := by
  unfold tailWord_2906285
  simp only [CollatzResearch.WordTrace]
  refine ⟨106000922276033273806352309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70667281517355515870901539 106000922276033273806352309)
  ·
    refine ⟨9937586463378119419345529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106000922276033273806352309 9937586463378119419345529)
    ·
      refine ⟨7453189847533589564509147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9937586463378119419345529 7453189847533589564509147)
      ·
        refine ⟨11179784771300384346763721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7453189847533589564509147 11179784771300384346763721)
        ·
          refine ⟨8384838578475288260072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11179784771300384346763721 8384838578475288260072791)
          ·
            refine ⟨12577257867712932390109187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384838578475288260072791 12577257867712932390109187)
            ·
              refine ⟨18865886801569398585163781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12577257867712932390109187 18865886801569398585163781)
              ·
                refine ⟨3537353775294262234718209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18865886801569398585163781 3537353775294262234718209)
                ·
                  refine ⟨2653015331470696676038657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3537353775294262234718209 2653015331470696676038657)
                  ·
                    refine ⟨1989761498603022507028993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653015331470696676038657 1989761498603022507028993)
                    ·
                      refine ⟨1492321123952266880271745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989761498603022507028993 1492321123952266880271745)
                      ·
                        rfl

theorem cell23_2906285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_2906285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906285 prefixEnd_2906285 := by exact prefixLift 2906285
  have htrace : WordTrace (prefixWord ++ tailWord_2906285) baseStart_2906285 baseEnd_2906285 := by
    simpa [prefixWord, tailWord_2906285, baseEnd_2906285] using wordTrace_append hprefix tailTrace_2906285
  have hstable : (prefixWord ++ tailWord_2906285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906285).length < 2 ^ (prefixWord ++ tailWord_2906285).sum := by decide
  have hdescent : baseEnd_2906285 < baseStart_2906285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906287 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 7]
def baseStart_2906287 : Nat := 118140960795 + 2906287 * 2 ^ 59
def prefixEnd_2906287 : Nat := 4983230072969 + 3 ^ 40 * 2906287 * 2
def baseEnd_2906287 : Nat := 497440716971191957482245

theorem tailTrace_2906287 : CollatzResearch.WordTrace tailWord_2906287 prefixEnd_2906287 497440716971191957482245 := by
  unfold tailWord_2906287
  simp only [CollatzResearch.WordTrace]
  refine ⟨106000995222026028147925115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70667330148017352098616743 106000995222026028147925115)
  ·
    refine ⟨159001492833039042221887673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106000995222026028147925115 159001492833039042221887673)
    ·
      refine ⟨119251119624779281666415755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159001492833039042221887673 119251119624779281666415755)
      ·
        refine ⟨178876679437168922499623633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119251119624779281666415755 178876679437168922499623633)
        ·
          refine ⟨134157509577876691874717725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178876679437168922499623633 134157509577876691874717725)
          ·
            refine ⟨50309066091703759453019147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134157509577876691874717725 50309066091703759453019147)
            ·
              refine ⟨75463599137555639179528721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50309066091703759453019147 75463599137555639179528721)
              ·
                refine ⟨56597699353166729384646541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75463599137555639179528721 56597699353166729384646541)
                ·
                  refine ⟨21224137257437523519242453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56597699353166729384646541 21224137257437523519242453)
                  ·
                    refine ⟨497440716971191957482245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21224137257437523519242453 497440716971191957482245)
                    ·
                      rfl

theorem cell23_2906287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_2906287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906287 prefixEnd_2906287 := by exact prefixLift 2906287
  have htrace : WordTrace (prefixWord ++ tailWord_2906287) baseStart_2906287 baseEnd_2906287 := by
    simpa [prefixWord, tailWord_2906287, baseEnd_2906287] using wordTrace_append hprefix tailTrace_2906287
  have hstable : (prefixWord ++ tailWord_2906287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906287).length < 2 ^ (prefixWord ++ tailWord_2906287).sum := by decide
  have hdescent : baseEnd_2906287 < baseStart_2906287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906351 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 3, 4]
def baseStart_2906351 : Nat := 118140960795 + 2906351 * 2 ^ 59
def prefixEnd_2906351 : Nat := 4983230072969 + 3 ^ 40 * 2906351 * 2
def baseEnd_2906351 : Nat := 497451671225154540682147

theorem tailTrace_2906351 : CollatzResearch.WordTrace tailWord_2906351 prefixEnd_2906351 497451671225154540682147 := by
  unfold tailWord_2906351
  simp only [CollatzResearch.WordTrace]
  refine ⟨106003329493794167078254907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70668886329196111385503271 106003329493794167078254907)
  ·
    refine ⟨159004994240691250617382361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106003329493794167078254907 159004994240691250617382361)
    ·
      refine ⟨119253745680518437963036771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159004994240691250617382361 119253745680518437963036771)
      ·
        refine ⟨178880618520777656944555157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119253745680518437963036771 178880618520777656944555157)
        ·
          refine ⟨8385028993161452669276023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178880618520777656944555157 8385028993161452669276023)
          ·
            refine ⟨12577543489742179003914035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385028993161452669276023 12577543489742179003914035)
            ·
              refine ⟨18866315234613268505871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12577543489742179003914035 18866315234613268505871053)
              ·
                refine ⟨7074868212979975689701645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18866315234613268505871053 7074868212979975689701645)
                ·
                  refine ⟨2653075579867490883638117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7074868212979975689701645 2653075579867490883638117)
                  ·
                    refine ⟨497451671225154540682147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653075579867490883638117 497451671225154540682147)
                    ·
                      rfl

theorem cell23_2906351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_2906351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906351 prefixEnd_2906351 := by exact prefixLift 2906351
  have htrace : WordTrace (prefixWord ++ tailWord_2906351) baseStart_2906351 baseEnd_2906351 := by
    simpa [prefixWord, tailWord_2906351, baseEnd_2906351] using wordTrace_append hprefix tailTrace_2906351
  have hstable : (prefixWord ++ tailWord_2906351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906351).length < 2 ^ (prefixWord ++ tailWord_2906351).sum := by decide
  have hdescent : baseEnd_2906351 < baseStart_2906351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906358 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2906358 : Nat := 118140960795 + 2906358 * 2 ^ 59
def prefixEnd_2906358 : Nat := 4983230072969 + 3 ^ 40 * 2906358 * 2
def baseEnd_2906358 : Nat := 1492358608040045094658909

theorem tailTrace_2906358 : CollatzResearch.WordTrace tailWord_2906358 prefixEnd_2906358 1492358608040045094658909 := by
  unfold tailWord_2906358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625224050298050454609983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70669056536512538182506485 6625224050298050454609983)
  ·
    refine ⟨9937836075447075681914975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625224050298050454609983 9937836075447075681914975)
    ·
      refine ⟨14906754113170613522872463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937836075447075681914975 14906754113170613522872463)
      ·
        refine ⟨22360131169755920284308695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906754113170613522872463 22360131169755920284308695)
        ·
          refine ⟨33540196754633880426463043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22360131169755920284308695 33540196754633880426463043)
          ·
            refine ⟨50310295131950820639694565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33540196754633880426463043 50310295131950820639694565)
            ·
              refine ⟨9433180337240778869942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50310295131950820639694565 9433180337240778869942731)
              ·
                refine ⟨14149770505861168304914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433180337240778869942731 14149770505861168304914097)
                ·
                  refine ⟨10612327879395876228685573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14149770505861168304914097 10612327879395876228685573)
                  ·
                    refine ⟨1989811477386726792878545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10612327879395876228685573 1989811477386726792878545)
                    ·
                      refine ⟨1492358608040045094658909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989811477386726792878545 1492358608040045094658909)
                      ·
                        rfl

theorem cell23_2906358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2906358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906358 prefixEnd_2906358 := by exact prefixLift 2906358
  have htrace : WordTrace (prefixWord ++ tailWord_2906358) baseStart_2906358 baseEnd_2906358 := by
    simpa [prefixWord, tailWord_2906358, baseEnd_2906358] using wordTrace_append hprefix tailTrace_2906358
  have hstable : (prefixWord ++ tailWord_2906358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906358).length < 2 ^ (prefixWord ++ tailWord_2906358).sum := by decide
  have hdescent : baseEnd_2906358 < baseStart_2906358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906385 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 1, 4]
def baseStart_2906385 : Nat := 118140960795 + 2906385 * 2 ^ 59
def prefixEnd_2906385 : Nat := 4983230072969 + 3 ^ 40 * 2906385 * 2
def baseEnd_2906385 : Nat := 497457490672572163007095

theorem tailTrace_2906385 : CollatzResearch.WordTrace tailWord_2906385 prefixEnd_2906385 497457490672572163007095 := by
  unfold tailWord_2906385
  simp only [CollatzResearch.WordTrace]
  refine ⟨106004569575670990884992609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70669713050447327256661739 106004569575670990884992609)
  ·
    refine ⟨79503427181753243163744457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106004569575670990884992609 79503427181753243163744457)
    ·
      refine ⟨59627570386314932372808343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79503427181753243163744457 59627570386314932372808343)
      ·
        refine ⟨89441355579472398559212515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59627570386314932372808343 89441355579472398559212515)
        ·
          refine ⟨134162033369208597838818773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89441355579472398559212515 134162033369208597838818773)
          ·
            refine ⟨3144422657090826511847315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134162033369208597838818773 3144422657090826511847315)
            ·
              refine ⟨4716633985636239767770973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144422657090826511847315 4716633985636239767770973)
              ·
                refine ⟨1768737744613589912914115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716633985636239767770973 1768737744613589912914115)
                ·
                  refine ⟨2653106616920384869371173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768737744613589912914115 2653106616920384869371173)
                  ·
                    refine ⟨497457490672572163007095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653106616920384869371173 497457490672572163007095)
                    ·
                      rfl

theorem cell23_2906385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_2906385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906385 prefixEnd_2906385 := by exact prefixLift 2906385
  have htrace : WordTrace (prefixWord ++ tailWord_2906385) baseStart_2906385 baseEnd_2906385 := by
    simpa [prefixWord, tailWord_2906385, baseEnd_2906385] using wordTrace_append hprefix tailTrace_2906385
  have hstable : (prefixWord ++ tailWord_2906385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906385).length < 2 ^ (prefixWord ++ tailWord_2906385).sum := by decide
  have hdescent : baseEnd_2906385 < baseStart_2906385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906398 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2906398 : Nat := 118140960795 + 2906398 * 2 ^ 59
def prefixEnd_2906398 : Nat := 4983230072969 + 3 ^ 40 * 2906398 * 2
def baseEnd_2906398 : Nat := 165819905251802770906525

theorem tailTrace_2906398 : CollatzResearch.WordTrace tailWord_2906398 prefixEnd_2906398 165819905251802770906525 := by
  unfold tailWord_2906398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250630465577986763151981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70670029149749262736810565 13250630465577986763151981)
  ·
    refine ⟨4968986424591745036181993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13250630465577986763151981 4968986424591745036181993)
    ·
      refine ⟨3726739818443808777136495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968986424591745036181993 3726739818443808777136495)
      ·
        refine ⟨5590109727665713165704743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726739818443808777136495 5590109727665713165704743)
        ·
          refine ⟨8385164591498569748557115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590109727665713165704743 8385164591498569748557115)
          ·
            refine ⟨12577746887247854622835673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385164591498569748557115 12577746887247854622835673)
            ·
              refine ⟨9433310165435890967126755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12577746887247854622835673 9433310165435890967126755)
              ·
                refine ⟨14149965248153836450690133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433310165435890967126755 14149965248153836450690133)
                ·
                  refine ⟨165819905251802770906525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14149965248153836450690133 165819905251802770906525)
                  ·
                    rfl

theorem cell23_2906398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2906398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906398 prefixEnd_2906398 := by exact prefixLift 2906398
  have htrace : WordTrace (prefixWord ++ tailWord_2906398) baseStart_2906398 baseEnd_2906398 := by
    simpa [prefixWord, tailWord_2906398, baseEnd_2906398] using wordTrace_append hprefix tailTrace_2906398
  have hstable : (prefixWord ++ tailWord_2906398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906398).length < 2 ^ (prefixWord ++ tailWord_2906398).sum := by decide
  have hdescent : baseEnd_2906398 < baseStart_2906398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906402 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2906402 : Nat := 118140960795 + 2906402 * 2 ^ 59
def prefixEnd_2906402 : Nat := 4983230072969 + 3 ^ 40 * 2906402 * 2
def baseEnd_2906402 : Nat := 497460400396280974169569

theorem tailTrace_2906402 : CollatzResearch.WordTrace tailWord_2906402 prefixEnd_2906402 497460400396280974169569 := by
  unfold tailWord_2906402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26501297404152350697090365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70670126411072935192240973 26501297404152350697090365)
  ·
    refine ⟨9937986526557131511408887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26501297404152350697090365 9937986526557131511408887)
    ·
      refine ⟨14906979789835697267113331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937986526557131511408887 14906979789835697267113331)
      ·
        refine ⟨22360469684753545900669997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906979789835697267113331 22360469684753545900669997)
        ·
          refine ⟨8385176131782579712751249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22360469684753545900669997 8385176131782579712751249)
          ·
            refine ⟨6288882098836934784563437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8385176131782579712751249 6288882098836934784563437)
            ·
              refine ⟨2358330787063850544211289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6288882098836934784563437 2358330787063850544211289)
              ·
                refine ⟨1768748090297887908158467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358330787063850544211289 1768748090297887908158467)
                ·
                  refine ⟨2653122135446831862237701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768748090297887908158467 2653122135446831862237701)
                  ·
                    refine ⟨497460400396280974169569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653122135446831862237701 497460400396280974169569)
                    ·
                      rfl

theorem cell23_2906402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2906402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906402 prefixEnd_2906402 := by exact prefixLift 2906402
  have htrace : WordTrace (prefixWord ++ tailWord_2906402) baseStart_2906402 baseEnd_2906402 := by
    simpa [prefixWord, tailWord_2906402, baseEnd_2906402] using wordTrace_append hprefix tailTrace_2906402
  have hstable : (prefixWord ++ tailWord_2906402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906402).length < 2 ^ (prefixWord ++ tailWord_2906402).sum := by decide
  have hdescent : baseEnd_2906402 < baseStart_2906402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906431 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_2906431 : Nat := 118140960795 + 2906431 * 2 ^ 59
def prefixEnd_2906431 : Nat := 4983230072969 + 3 ^ 40 * 2906431 * 2
def baseEnd_2906431 : Nat := 1492396092127823309046073

theorem tailTrace_2906431 : CollatzResearch.WordTrace tailWord_2906431 prefixEnd_2906431 1492396092127823309046073 := by
  unfold tailWord_2906431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106006247333504340741167147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70670831555669560494111431 106006247333504340741167147)
  ·
    refine ⟨159009371000256511111750721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106006247333504340741167147 159009371000256511111750721)
    ·
      refine ⟨119257028250192383333813041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159009371000256511111750721 119257028250192383333813041)
      ·
        refine ⟨89442771187644287500359781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119257028250192383333813041 89442771187644287500359781)
        ·
          refine ⟨16770519597683303906317459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89442771187644287500359781 16770519597683303906317459)
          ·
            refine ⟨25155779396524955859476189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16770519597683303906317459 25155779396524955859476189)
            ·
              refine ⟨9433417273696858447303571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25155779396524955859476189 9433417273696858447303571)
              ·
                refine ⟨14150125910545287670955357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433417273696858447303571 14150125910545287670955357)
                ·
                  refine ⟨5306297216454482876608259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14150125910545287670955357 5306297216454482876608259)
                  ·
                    refine ⟨7959445824681724314912389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306297216454482876608259 7959445824681724314912389)
                    ·
                      refine ⟨1492396092127823309046073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7959445824681724314912389 1492396092127823309046073)
                      ·
                        rfl

theorem cell23_2906431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_2906431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906431 prefixEnd_2906431 := by exact prefixLift 2906431
  have htrace : WordTrace (prefixWord ++ tailWord_2906431) baseStart_2906431 baseEnd_2906431 := by
    simpa [prefixWord, tailWord_2906431, baseEnd_2906431] using wordTrace_append hprefix tailTrace_2906431
  have hstable : (prefixWord ++ tailWord_2906431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906431).length < 2 ^ (prefixWord ++ tailWord_2906431).sum := by decide
  have hdescent : baseEnd_2906431 < baseStart_2906431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906471 : List Nat := [1, 1, 5, 1, 3, 1, 3, 8]
def baseStart_2906471 : Nat := 118140960795 + 2906471 * 2 ^ 59
def prefixEnd_2906471 : Nat := 4983230072969 + 3 ^ 40 * 2906471 * 2
def baseEnd_2906471 : Nat := 55274690050148264909107

theorem tailTrace_2906471 : CollatzResearch.WordTrace tailWord_2906471 prefixEnd_2906471 55274690050148264909107 := by
  unfold tailWord_2906471
  simp only [CollatzResearch.WordTrace]
  refine ⟨106007706253359427572623267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70671804168906285048415511 106007706253359427572623267)
  ·
    refine ⟨159011559380039141358934901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106007706253359427572623267 159011559380039141358934901)
    ·
      refine ⟨14907333691878669502400147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159011559380039141358934901 14907333691878669502400147)
      ·
        refine ⟨22361000537818004253600221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14907333691878669502400147 22361000537818004253600221)
        ·
          refine ⟨8385375201681751595100083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22361000537818004253600221 8385375201681751595100083)
          ·
            refine ⟨12578062802522627392650125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385375201681751595100083 12578062802522627392650125)
            ·
              refine ⟨4716773550945985272243797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12578062802522627392650125 4716773550945985272243797)
              ·
                refine ⟨55274690050148264909107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4716773550945985272243797 55274690050148264909107)
                ·
                  rfl

theorem cell23_2906471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 8].length) (baseStart_2906471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906471 prefixEnd_2906471 := by exact prefixLift 2906471
  have htrace : WordTrace (prefixWord ++ tailWord_2906471) baseStart_2906471 baseEnd_2906471 := by
    simpa [prefixWord, tailWord_2906471, baseEnd_2906471] using wordTrace_append hprefix tailTrace_2906471
  have hstable : (prefixWord ++ tailWord_2906471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906471).length < 2 ^ (prefixWord ++ tailWord_2906471).sum := by decide
  have hdescent : baseEnd_2906471 < baseStart_2906471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906486 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2906486 : Nat := 118140960795 + 2906486 * 2 ^ 59
def prefixEnd_2906486 : Nat := 4983230072969 + 3 ^ 40 * 2906486 * 2
def baseEnd_2906486 : Nat := 1492424333563820593858321

theorem tailTrace_2906486 : CollatzResearch.WordTrace tailWord_2906486 prefixEnd_2906486 1492424333563820593858321 := by
  unfold tailWord_2906486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625515834269067820901207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70672168898870056756279541 6625515834269067820901207)
  ·
    refine ⟨9938273751403601731351811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625515834269067820901207 9938273751403601731351811)
    ·
      refine ⟨14907410627105402597027717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9938273751403601731351811 14907410627105402597027717)
      ·
        refine ⟨2795139492582262986942697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14907410627105402597027717 2795139492582262986942697)
        ·
          refine ⟨2096354619436697240207023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795139492582262986942697 2096354619436697240207023)
          ·
            refine ⟨3144531929155045860310535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096354619436697240207023 3144531929155045860310535)
            ·
              refine ⟨4716797893732568790465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144531929155045860310535 4716797893732568790465803)
              ·
                refine ⟨7075196840598853185698705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716797893732568790465803 7075196840598853185698705)
                ·
                  refine ⟨5306397630449139889274029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7075196840598853185698705 5306397630449139889274029)
                  ·
                    refine ⟨1989899111418427458477761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5306397630449139889274029 1989899111418427458477761)
                    ·
                      refine ⟨1492424333563820593858321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989899111418427458477761 1492424333563820593858321)
                      ·
                        rfl

theorem cell23_2906486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2906486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906486 prefixEnd_2906486 := by exact prefixLift 2906486
  have htrace : WordTrace (prefixWord ++ tailWord_2906486) baseStart_2906486 baseEnd_2906486 := by
    simpa [prefixWord, tailWord_2906486, baseEnd_2906486] using wordTrace_append hprefix tailTrace_2906486
  have hstable : (prefixWord ++ tailWord_2906486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906486).length < 2 ^ (prefixWord ++ tailWord_2906486).sum := by decide
  have hdescent : baseEnd_2906486 < baseStart_2906486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906499 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 1, 2, 2]
def baseStart_2906499 : Nat := 118140960795 + 2906499 * 2 ^ 59
def prefixEnd_2906499 : Nat := 4983230072969 + 3 ^ 40 * 2906499 * 2
def baseEnd_2906499 : Nat := 1492431008812329042995761

theorem tailTrace_2906499 : CollatzResearch.WordTrace tailWord_2906499 prefixEnd_2906499 1492431008812329042995761 := by
  unfold tailWord_2906499
  simp only [CollatzResearch.WordTrace]
  refine ⟨106008727497257988354642551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70672484998171992236428367 106008727497257988354642551)
  ·
    refine ⟨159013091245886982531963827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106008727497257988354642551 159013091245886982531963827)
    ·
      refine ⟨238519636868830473797945741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159013091245886982531963827 238519636868830473797945741)
      ·
        refine ⟨89444863825811427674229653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238519636868830473797945741 89444863825811427674229653)
        ·
          refine ⟨4192727991834910672229515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89444863825811427674229653 4192727991834910672229515)
          ·
            refine ⟨6289091987752366008344273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192727991834910672229515 6289091987752366008344273)
            ·
              refine ⟨4716818990814274506258205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6289091987752366008344273 4716818990814274506258205)
              ·
                refine ⟨1768807121555352939846827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716818990814274506258205 1768807121555352939846827)
                ·
                  refine ⟨2653210682333029409770241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768807121555352939846827 2653210682333029409770241)
                  ·
                    refine ⟨1989908011749772057327681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653210682333029409770241 1989908011749772057327681)
                    ·
                      refine ⟨1492431008812329042995761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1989908011749772057327681 1492431008812329042995761)
                      ·
                        rfl

theorem cell23_2906499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_2906499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906499 prefixEnd_2906499 := by exact prefixLift 2906499
  have htrace : WordTrace (prefixWord ++ tailWord_2906499) baseStart_2906499 baseEnd_2906499 := by
    simpa [prefixWord, tailWord_2906499, baseEnd_2906499] using wordTrace_append hprefix tailTrace_2906499
  have hstable : (prefixWord ++ tailWord_2906499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906499).length < 2 ^ (prefixWord ++ tailWord_2906499).sum := by decide
  have hdescent : baseEnd_2906499 < baseStart_2906499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906531 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 6]
def baseStart_2906531 : Nat := 118140960795 + 2906531 * 2 ^ 59
def prefixEnd_2906531 : Nat := 4983230072969 + 3 ^ 40 * 2906531 * 2
def baseEnd_2906531 : Nat := 497482480064424305931871

theorem tailTrace_2906531 : CollatzResearch.WordTrace tailWord_2906531 prefixEnd_2906531 497482480064424305931871 := by
  unfold tailWord_2906531
  simp only [CollatzResearch.WordTrace]
  refine ⟨106009894633142057819807447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70673263088761371879871631 106009894633142057819807447)
  ·
    refine ⟨159014841949713086729711171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106009894633142057819807447 159014841949713086729711171)
    ·
      refine ⟨238522262924569630094566757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159014841949713086729711171 238522262924569630094566757)
      ·
        refine ⟨44722924298356805642731267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238522262924569630094566757 44722924298356805642731267)
        ·
          refine ⟨67084386447535208464096901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44722924298356805642731267 67084386447535208464096901)
          ·
            refine ⟨12578322458912851587018169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67084386447535208464096901 12578322458912851587018169)
            ·
              refine ⟨9433741844184638690263627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12578322458912851587018169 9433741844184638690263627)
              ·
                refine ⟨14150612766276958035395441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433741844184638690263627 14150612766276958035395441)
                ·
                  refine ⟨10612959574707718526546581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14150612766276958035395441 10612959574707718526546581)
                  ·
                    refine ⟨497482480064424305931871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10612959574707718526546581 497482480064424305931871)
                    ·
                      rfl

theorem cell23_2906531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_2906531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906531 prefixEnd_2906531 := by exact prefixLift 2906531
  have htrace : WordTrace (prefixWord ++ tailWord_2906531) baseStart_2906531 baseEnd_2906531 := by
    simpa [prefixWord, tailWord_2906531, baseEnd_2906531] using wordTrace_append hprefix tailTrace_2906531
  have hstable : (prefixWord ++ tailWord_2906531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906531).length < 2 ^ (prefixWord ++ tailWord_2906531).sum := by decide
  have hdescent : baseEnd_2906531 < baseStart_2906531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906608 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_2906608 : Nat := 118140960795 + 2906608 * 2 ^ 59
def prefixEnd_2906608 : Nat := 4983230072969 + 3 ^ 40 * 2906608 * 2
def baseEnd_2906608 : Nat := 497495659401223038844253

theorem tailTrace_2906608 : CollatzResearch.WordTrace tailWord_2906608 prefixEnd_2906608 497495659401223038844253 := by
  unfold tailWord_2906608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53006351526931549985180239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70675135369242066646906985 53006351526931549985180239)
  ·
    refine ⟨79509527290397324977770359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53006351526931549985180239 79509527290397324977770359)
    ·
      refine ⟨119264290935595987466655539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79509527290397324977770359 119264290935595987466655539)
      ·
        refine ⟨178896436403393981199983309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119264290935595987466655539 178896436403393981199983309)
        ·
          refine ⟨67086163651272742949993741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178896436403393981199983309 67086163651272742949993741)
          ·
            refine ⟨25157311369227278606247653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67086163651272742949993741 25157311369227278606247653)
            ·
              refine ⟨4716995881730114738671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25157311369227278606247653 4716995881730114738671435)
              ·
                refine ⟨7075493822595172108007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716995881730114738671435 7075493822595172108007153)
                ·
                  refine ⟨5306620366946379081005365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7075493822595172108007153 5306620366946379081005365)
                  ·
                    refine ⟨497495659401223038844253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5306620366946379081005365 497495659401223038844253)
                    ·
                      rfl

theorem cell23_2906608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_2906608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906608 prefixEnd_2906608 := by exact prefixLift 2906608
  have htrace : WordTrace (prefixWord ++ tailWord_2906608) baseStart_2906608 baseEnd_2906608 := by
    simpa [prefixWord, tailWord_2906608, baseEnd_2906608] using wordTrace_append hprefix tailTrace_2906608
  have hstable : (prefixWord ++ tailWord_2906608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906608).length < 2 ^ (prefixWord ++ tailWord_2906608).sum := by decide
  have hdescent : baseEnd_2906608 < baseStart_2906608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906641 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2906641 : Nat := 118140960795 + 2906641 * 2 ^ 59
def prefixEnd_2906641 : Nat := 4983230072969 + 3 ^ 40 * 2906641 * 2
def baseEnd_2906641 : Nat := 1492503923065267487420107

theorem tailTrace_2906641 : CollatzResearch.WordTrace tailWord_2906641 prefixEnd_2906641 1492503923065267487420107 := by
  unfold tailWord_2906641
  simp only [CollatzResearch.WordTrace]
  refine ⟨106013906662743546606311777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70675937775162364404207851 106013906662743546606311777)
  ·
    refine ⟨79510429997057659954733833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106013906662743546606311777 79510429997057659954733833)
    ·
      refine ⟨59632822497793244966050375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79510429997057659954733833 59632822497793244966050375)
      ·
        refine ⟨89449233746689867449075563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59632822497793244966050375 89449233746689867449075563)
        ·
          refine ⟨134173850620034801173613345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89449233746689867449075563 134173850620034801173613345)
          ·
            refine ⟨100630387965026100880210009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134173850620034801173613345 100630387965026100880210009)
            ·
              refine ⟨75472790973769575660157507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100630387965026100880210009 75472790973769575660157507)
              ·
                refine ⟨113209186460654363490236261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75472790973769575660157507 113209186460654363490236261)
                ·
                  refine ⟨21226722461372693154419299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113209186460654363490236261 21226722461372693154419299)
                  ·
                    refine ⟨31840083692059039731628949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21226722461372693154419299 31840083692059039731628949)
                    ·
                      refine ⟨1492503923065267487420107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31840083692059039731628949 1492503923065267487420107)
                      ·
                        rfl

theorem cell23_2906641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2906641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906641 prefixEnd_2906641 := by exact prefixLift 2906641
  have htrace : WordTrace (prefixWord ++ tailWord_2906641) baseStart_2906641 baseEnd_2906641 := by
    simpa [prefixWord, tailWord_2906641, baseEnd_2906641] using wordTrace_append hprefix tailTrace_2906641
  have hstable : (prefixWord ++ tailWord_2906641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906641).length < 2 ^ (prefixWord ++ tailWord_2906641).sum := by decide
  have hdescent : baseEnd_2906641 < baseStart_2906641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906645 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_2906645 : Nat := 118140960795 + 2906645 * 2 ^ 59
def prefixEnd_2906645 : Nat := 4983230072969 + 3 ^ 40 * 2906645 * 2
def baseEnd_2906645 : Nat := 1492505976987885471770089

theorem tailTrace_2906645 : CollatzResearch.WordTrace tailWord_2906645 prefixEnd_2906645 1492505976987885471770089 := by
  unfold tailWord_2906645
  simp only [CollatzResearch.WordTrace]
  refine ⟨106014052554729055289457389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70676035036486036859638259 106014052554729055289457389)
  ·
    refine ⟨39755269708023395733546521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106014052554729055289457389 39755269708023395733546521)
    ·
      refine ⟨29816452281017546800159891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39755269708023395733546521 29816452281017546800159891)
      ·
        refine ⟨44724678421526320200239837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29816452281017546800159891 44724678421526320200239837)
        ·
          refine ⟨16771754408072370075089939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44724678421526320200239837 16771754408072370075089939)
          ·
            refine ⟨25157631612108555112634909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771754408072370075089939 25157631612108555112634909)
            ·
              refine ⟨9434111854540708167238091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25157631612108555112634909 9434111854540708167238091)
              ·
                refine ⟨14151167781811062250857137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434111854540708167238091 14151167781811062250857137)
                ·
                  refine ⟨10613375836358296688142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14151167781811062250857137 10613375836358296688142853)
                  ·
                    refine ⟨1990007969317180629026785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10613375836358296688142853 1990007969317180629026785)
                    ·
                      refine ⟨1492505976987885471770089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990007969317180629026785 1492505976987885471770089)
                      ·
                        rfl

theorem cell23_2906645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_2906645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906645 prefixEnd_2906645 := by exact prefixLift 2906645
  have htrace : WordTrace (prefixWord ++ tailWord_2906645) baseStart_2906645 baseEnd_2906645 := by
    simpa [prefixWord, tailWord_2906645, baseEnd_2906645] using wordTrace_append hprefix tailTrace_2906645
  have hstable : (prefixWord ++ tailWord_2906645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906645).length < 2 ^ (prefixWord ++ tailWord_2906645).sum := by decide
  have hdescent : baseEnd_2906645 < baseStart_2906645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906671 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_2906671 : Nat := 118140960795 + 2906671 * 2 ^ 59
def prefixEnd_2906671 : Nat := 4983230072969 + 3 ^ 40 * 2906671 * 2
def baseEnd_2906671 : Nat := 1492519327484902370044969

theorem tailTrace_2906671 : CollatzResearch.WordTrace tailWord_2906671 prefixEnd_2906671 1492519327484902370044969 := by
  unfold tailWord_2906671
  simp only [CollatzResearch.WordTrace]
  refine ⟨106015000852634861729903867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70676667235089907819935911 106015000852634861729903867)
  ·
    refine ⟨159022501278952292594855801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106015000852634861729903867 159022501278952292594855801)
    ·
      refine ⟨119266875959214219446141851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159022501278952292594855801 119266875959214219446141851)
      ·
        refine ⟨178900313938821329169212777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119266875959214219446141851 178900313938821329169212777)
        ·
          refine ⟨134175235454115996876909583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178900313938821329169212777 134175235454115996876909583)
          ·
            refine ⟨201262853181173995315364375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134175235454115996876909583 201262853181173995315364375)
            ·
              refine ⟨301894279771760992973046563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201262853181173995315364375 301894279771760992973046563)
              ·
                refine ⟨452841419657641489459569845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301894279771760992973046563 452841419657641489459569845)
                ·
                  refine ⟨42453883092903889636834673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452841419657641489459569845 42453883092903889636834673)
                  ·
                    refine ⟨31840412319677917227626005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42453883092903889636834673 31840412319677917227626005)
                    ·
                      refine ⟨1492519327484902370044969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31840412319677917227626005 1492519327484902370044969)
                      ·
                        rfl

theorem cell23_2906671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_2906671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906671 prefixEnd_2906671 := by exact prefixLift 2906671
  have htrace : WordTrace (prefixWord ++ tailWord_2906671) baseStart_2906671 baseEnd_2906671 := by
    simpa [prefixWord, tailWord_2906671, baseEnd_2906671] using wordTrace_append hprefix tailTrace_2906671
  have hstable : (prefixWord ++ tailWord_2906671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906671).length < 2 ^ (prefixWord ++ tailWord_2906671).sum := by decide
  have hdescent : baseEnd_2906671 < baseStart_2906671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906685 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 6]
def baseStart_2906685 : Nat := 118140960795 + 2906685 * 2 ^ 59
def prefixEnd_2906685 : Nat := 4983230072969 + 3 ^ 40 * 2906685 * 2
def baseEnd_2906685 : Nat := 165836279579340590585545

theorem tailTrace_2906685 : CollatzResearch.WordTrace tailWord_2906685 prefixEnd_2906685 165836279579340590585545 := by
  unfold tailWord_2906685
  simp only [CollatzResearch.WordTrace]
  refine ⟨106015511474584142120913509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70677007649722761413942339 106015511474584142120913509)
  ·
    refine ⟨19877908401484526647671283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106015511474584142120913509 19877908401484526647671283)
    ·
      refine ⟨29816862602226789971506925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19877908401484526647671283 29816862602226789971506925)
      ·
        refine ⟨11181323475835046239315097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29816862602226789971506925 11181323475835046239315097)
        ·
          refine ⟨8385992606876284679486323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11181323475835046239315097 8385992606876284679486323)
          ·
            refine ⟨12578988910314427019229485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385992606876284679486323 12578988910314427019229485)
            ·
              refine ⟨4717120841367910132211057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12578988910314427019229485 4717120841367910132211057)
              ·
                refine ⟨3537840631025932599158293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717120841367910132211057 3537840631025932599158293)
                ·
                  refine ⟨165836279579340590585545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3537840631025932599158293 165836279579340590585545)
                  ·
                    rfl

theorem cell23_2906685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_2906685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906685 prefixEnd_2906685 := by exact prefixLift 2906685
  have htrace : WordTrace (prefixWord ++ tailWord_2906685) baseStart_2906685 baseEnd_2906685 := by
    simpa [prefixWord, tailWord_2906685, baseEnd_2906685] using wordTrace_append hprefix tailTrace_2906685
  have hstable : (prefixWord ++ tailWord_2906685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906685).length < 2 ^ (prefixWord ++ tailWord_2906685).sum := by decide
  have hdescent : baseEnd_2906685 < baseStart_2906685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906705 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_2906705 : Nat := 118140960795 + 2906705 * 2 ^ 59
def prefixEnd_2906705 : Nat := 4983230072969 + 3 ^ 40 * 2906705 * 2
def baseEnd_2906705 : Nat := 1492536785827155237019813

theorem tailTrace_2906705 : CollatzResearch.WordTrace tailWord_2906705 prefixEnd_2906705 1492536785827155237019813 := by
  unfold tailWord_2906705
  simp only [CollatzResearch.WordTrace]
  refine ⟨106016240934511685536641569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70677493956341123691094379 106016240934511685536641569)
  ·
    refine ⟨79512180700883764152481177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106016240934511685536641569 79512180700883764152481177)
    ·
      refine ⟨59634135525662823114360883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79512180700883764152481177 59634135525662823114360883)
      ·
        refine ⟨89451203288494234671541325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59634135525662823114360883 89451203288494234671541325)
        ·
          refine ⟨33544201233185338001827997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89451203288494234671541325 33544201233185338001827997)
          ·
            refine ⟨12579075462444501750685499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33544201233185338001827997 12579075462444501750685499)
            ·
              refine ⟨18868613193666752626028249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579075462444501750685499 18868613193666752626028249)
              ·
                refine ⟨14151459895250064469521187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18868613193666752626028249 14151459895250064469521187)
                ·
                  refine ⟨21227189842875096704281781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14151459895250064469521187 21227189842875096704281781)
                  ·
                    refine ⟨1990049047769540316026417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21227189842875096704281781 1990049047769540316026417)
                    ·
                      refine ⟨1492536785827155237019813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990049047769540316026417 1492536785827155237019813)
                      ·
                        rfl

theorem cell23_2906705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_2906705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906705 prefixEnd_2906705 := by exact prefixLift 2906705
  have htrace : WordTrace (prefixWord ++ tailWord_2906705) baseStart_2906705 baseEnd_2906705 := by
    simpa [prefixWord, tailWord_2906705, baseEnd_2906705] using wordTrace_append hprefix tailTrace_2906705
  have hstable : (prefixWord ++ tailWord_2906705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906705).length < 2 ^ (prefixWord ++ tailWord_2906705).sum := by decide
  have hdescent : baseEnd_2906705 < baseStart_2906705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906735 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_2906735 : Nat := 118140960795 + 2906735 * 2 ^ 59
def prefixEnd_2906735 : Nat := 4983230072969 + 3 ^ 40 * 2906735 * 2
def baseEnd_2906735 : Nat := 1492552190246790119644675

theorem tailTrace_2906735 : CollatzResearch.WordTrace tailWord_2906735 prefixEnd_2906735 1492552190246790119644675 := by
  unfold tailWord_2906735
  simp only [CollatzResearch.WordTrace]
  refine ⟨106017335124403000660233659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70678223416268667106822439 106017335124403000660233659)
  ·
    refine ⟨159026002686604500990350489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106017335124403000660233659 159026002686604500990350489)
    ·
      refine ⟨119269502014953375742762867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159026002686604500990350489 119269502014953375742762867)
      ·
        refine ⟨178904253022430063614144301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119269502014953375742762867 178904253022430063614144301)
        ·
          refine ⟨67089094883411273855304113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178904253022430063614144301 67089094883411273855304113)
          ·
            refine ⟨50316821162558455391478085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67089094883411273855304113 50316821162558455391478085)
            ·
              refine ⟨9434403967979710385902141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50316821162558455391478085 9434403967979710385902141)
              ·
                refine ⟨3537901487992391394713303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9434403967979710385902141 3537901487992391394713303)
                ·
                  refine ⟨5306852231988587092069955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537901487992391394713303 5306852231988587092069955)
                  ·
                    refine ⟨7960278347982880638104933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306852231988587092069955 7960278347982880638104933)
                    ·
                      refine ⟨1492552190246790119644675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7960278347982880638104933 1492552190246790119644675)
                      ·
                        rfl

theorem cell23_2906735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_2906735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906735 prefixEnd_2906735 := by exact prefixLift 2906735
  have htrace : WordTrace (prefixWord ++ tailWord_2906735) baseStart_2906735 baseEnd_2906735 := by
    simpa [prefixWord, tailWord_2906735, baseEnd_2906735] using wordTrace_append hprefix tailTrace_2906735
  have hstable : (prefixWord ++ tailWord_2906735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906735).length < 2 ^ (prefixWord ++ tailWord_2906735).sum := by decide
  have hdescent : baseEnd_2906735 < baseStart_2906735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906745 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_2906745 : Nat := 118140960795 + 2906745 * 2 ^ 59
def prefixEnd_2906745 : Nat := 4983230072969 + 3 ^ 40 * 2906745 * 2
def baseEnd_2906745 : Nat := 497519108351111693506543

theorem tailTrace_2906745 : CollatzResearch.WordTrace tailWord_2906745 prefixEnd_2906745 497519108351111693506543 := by
  unfold tailWord_2906745
  simp only [CollatzResearch.WordTrace]
  refine ⟨106017699854366772368097689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70678466569577848245398459 106017699854366772368097689)
  ·
    refine ⟨79513274890775079276073267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106017699854366772368097689 79513274890775079276073267)
    ·
      refine ⟨119269912336162618914109901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79513274890775079276073267 119269912336162618914109901)
      ·
        refine ⟨44726217126060982092791213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119269912336162618914109901 44726217126060982092791213)
        ·
          refine ⟨16772331422272868284796705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44726217126060982092791213 16772331422272868284796705)
          ·
            refine ⟨12579248566704651213597529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16772331422272868284796705 12579248566704651213597529)
            ·
              refine ⟨9434436425028488410198147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12579248566704651213597529 9434436425028488410198147)
              ·
                refine ⟨14151654637542732615297221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434436425028488410198147 14151654637542732615297221)
                ·
                  refine ⟨2653435244539262365368229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14151654637542732615297221 2653435244539262365368229)
                  ·
                    refine ⟨497519108351111693506543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2653435244539262365368229 497519108351111693506543)
                    ·
                      rfl

theorem cell23_2906745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_2906745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906745 prefixEnd_2906745 := by exact prefixLift 2906745
  have htrace : WordTrace (prefixWord ++ tailWord_2906745) baseStart_2906745 baseEnd_2906745 := by
    simpa [prefixWord, tailWord_2906745, baseEnd_2906745] using wordTrace_append hprefix tailTrace_2906745
  have hstable : (prefixWord ++ tailWord_2906745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906745).length < 2 ^ (prefixWord ++ tailWord_2906745).sum := by decide
  have hdescent : baseEnd_2906745 < baseStart_2906745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906748 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2906748 : Nat := 118140960795 + 2906748 * 2 ^ 59
def prefixEnd_2906748 : Nat := 4983230072969 + 3 ^ 40 * 2906748 * 2
def baseEnd_2906748 : Nat := 1492558865495298568782115

theorem tailTrace_2906748 : CollatzResearch.WordTrace tailWord_2906748 prefixEnd_2906748 1492558865495298568782115 := by
  unfold tailWord_2906748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53008904636677951940228449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70678539515570602586971265 53008904636677951940228449)
  ·
    refine ⟨39756678477508463955171337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53008904636677951940228449 39756678477508463955171337)
    ·
      refine ⟨29817508858131347966378503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39756678477508463955171337 29817508858131347966378503)
      ·
        refine ⟨44726263287197021949567755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29817508858131347966378503 44726263287197021949567755)
        ·
          refine ⟨67089394930795532924351633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44726263287197021949567755 67089394930795532924351633)
          ·
            refine ⟨50317046198096649693263725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67089394930795532924351633 50317046198096649693263725)
            ·
              refine ⟨18868892324286243634973897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50317046198096649693263725 18868892324286243634973897)
              ·
                refine ⟨14151669243214682726230423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18868892324286243634973897 14151669243214682726230423)
                ·
                  refine ⟨21227503864822024089345635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14151669243214682726230423 21227503864822024089345635)
                  ·
                    refine ⟨31841255797233036134018453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21227503864822024089345635 31841255797233036134018453)
                    ·
                      refine ⟨1492558865495298568782115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31841255797233036134018453 1492558865495298568782115)
                      ·
                        rfl

theorem cell23_2906748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2906748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906748 prefixEnd_2906748 := by exact prefixLift 2906748
  have htrace : WordTrace (prefixWord ++ tailWord_2906748) baseStart_2906748 baseEnd_2906748 := by
    simpa [prefixWord, tailWord_2906748, baseEnd_2906748] using wordTrace_append hprefix tailTrace_2906748
  have hstable : (prefixWord ++ tailWord_2906748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906748).length < 2 ^ (prefixWord ++ tailWord_2906748).sum := by decide
  have hdescent : baseEnd_2906748 < baseStart_2906748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906782 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2906782 : Nat := 118140960795 + 2906782 * 2 ^ 59
def prefixEnd_2906782 : Nat := 4983230072969 + 3 ^ 40 * 2906782 * 2
def baseEnd_2906782 : Nat := 1492576323837551435756959

theorem tailTrace_2906782 : CollatzResearch.WordTrace tailWord_2906782 prefixEnd_2906782 1492576323837551435756959 := by
  unfold tailWord_2906782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13252381169404090960899325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70679366236821818458129733 13252381169404090960899325)
  ·
    refine ⟨4969642938526534110337247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13252381169404090960899325 4969642938526534110337247)
    ·
      refine ⟨7454464407789801165505871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4969642938526534110337247 7454464407789801165505871)
      ·
        refine ⟨11181696611684701748258807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7454464407789801165505871 11181696611684701748258807)
        ·
          refine ⟨16772544917527052622388211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181696611684701748258807 16772544917527052622388211)
          ·
            refine ⟨25158817376290578933582317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16772544917527052622388211 25158817376290578933582317)
            ·
              refine ⟨9434556516108967100093369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25158817376290578933582317 9434556516108967100093369)
              ·
                refine ⟨7075917387081725325070027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434556516108967100093369 7075917387081725325070027)
                ·
                  refine ⟨10613876080622587987605041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7075917387081725325070027 10613876080622587987605041)
                  ·
                    refine ⟨7960407060466940990703781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10613876080622587987605041 7960407060466940990703781)
                    ·
                      refine ⟨1492576323837551435756959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7960407060466940990703781 1492576323837551435756959)
                      ·
                        rfl

theorem cell23_2906782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2906782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906782 prefixEnd_2906782 := by exact prefixLift 2906782
  have htrace : WordTrace (prefixWord ++ tailWord_2906782) baseStart_2906782 baseEnd_2906782 := by
    simpa [prefixWord, tailWord_2906782, baseEnd_2906782] using wordTrace_append hprefix tailTrace_2906782
  have hstable : (prefixWord ++ tailWord_2906782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906782).length < 2 ^ (prefixWord ++ tailWord_2906782).sum := by decide
  have hdescent : baseEnd_2906782 < baseStart_2906782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906803 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 1, 2, 2]
def baseStart_2906803 : Nat := 118140960795 + 2906803 * 2 ^ 59
def prefixEnd_2906803 : Nat := 4983230072969 + 3 ^ 40 * 2906803 * 2
def baseEnd_2906803 : Nat := 1492587106931295853594363

theorem tailTrace_2906803 : CollatzResearch.WordTrace tailWord_2906803 prefixEnd_2906803 1492587106931295853594363 := by
  unfold tailWord_2906803
  simp only [CollatzResearch.WordTrace]
  refine ⟨106019815288156648273709063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70679876858771098849139375 106019815288156648273709063)
  ·
    refine ⟨159029722932234972410563595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106019815288156648273709063 159029722932234972410563595)
    ·
      refine ⟨238544584398352458615845393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159029722932234972410563595 238544584398352458615845393)
      ·
        refine ⟨178908438298764343961884045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238544584398352458615845393 178908438298764343961884045)
        ·
          refine ⟨67090664362036628985706517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178908438298764343961884045 67090664362036628985706517)
          ·
            refine ⟨3144874891970466983704993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67090664362036628985706517 3144874891970466983704993)
            ·
              refine ⟨2358656168977850237778745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144874891970466983704993 2358656168977850237778745)
              ·
                refine ⟨1768992126733387678334059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358656168977850237778745 1768992126733387678334059)
                ·
                  refine ⟨2653488190100081517501089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768992126733387678334059 2653488190100081517501089)
                  ·
                    refine ⟨1990116142575061138125817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653488190100081517501089 1990116142575061138125817)
                    ·
                      refine ⟨1492587106931295853594363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990116142575061138125817 1492587106931295853594363)
                      ·
                        rfl

theorem cell23_2906803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 2, 2].length) (baseStart_2906803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906803 prefixEnd_2906803 := by exact prefixLift 2906803
  have htrace : WordTrace (prefixWord ++ tailWord_2906803) baseStart_2906803 baseEnd_2906803 := by
    simpa [prefixWord, tailWord_2906803, baseEnd_2906803] using wordTrace_append hprefix tailTrace_2906803
  have hstable : (prefixWord ++ tailWord_2906803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906803).length < 2 ^ (prefixWord ++ tailWord_2906803).sum := by decide
  have hdescent : baseEnd_2906803 < baseStart_2906803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906805 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2906805 : Nat := 118140960795 + 2906805 * 2 ^ 59
def prefixEnd_2906805 : Nat := 4983230072969 + 3 ^ 40 * 2906805 * 2
def baseEnd_2906805 : Nat := 497529377964201615256451

theorem tailTrace_2906805 : CollatzResearch.WordTrace tailWord_2906805 prefixEnd_2906805 497529377964201615256451 := by
  unfold tailWord_2906805
  simp only [CollatzResearch.WordTrace]
  refine ⟨106019888234149402615281869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70679925489432935076854579 106019888234149402615281869)
  ·
    refine ⟨39757458087806025980730701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106019888234149402615281869 39757458087806025980730701)
    ·
      refine ⟨14909046782927259742774013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39757458087806025980730701 14909046782927259742774013)
      ·
        refine ⟨5590892543597722403540255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14909046782927259742774013 5590892543597722403540255)
        ·
          refine ⟨8386338815396583605310383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590892543597722403540255 8386338815396583605310383)
          ·
            refine ⟨12579508223094875407965575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386338815396583605310383 12579508223094875407965575)
            ·
              refine ⟨18869262334642313111948363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579508223094875407965575 18869262334642313111948363)
              ·
                refine ⟨28303893501963469667922545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18869262334642313111948363 28303893501963469667922545)
                ·
                  refine ⟨21227920126472602250941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28303893501963469667922545 21227920126472602250941909)
                  ·
                    refine ⟨497529377964201615256451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21227920126472602250941909 497529377964201615256451)
                    ·
                      rfl

theorem cell23_2906805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2906805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906805 prefixEnd_2906805 := by exact prefixLift 2906805
  have htrace : WordTrace (prefixWord ++ tailWord_2906805) baseStart_2906805 baseEnd_2906805 := by
    simpa [prefixWord, tailWord_2906805, baseEnd_2906805] using wordTrace_append hprefix tailTrace_2906805
  have hstable : (prefixWord ++ tailWord_2906805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906805).length < 2 ^ (prefixWord ++ tailWord_2906805).sum := by decide
  have hdescent : baseEnd_2906805 < baseStart_2906805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906812 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2906812 : Nat := 118140960795 + 2906812 * 2 ^ 59
def prefixEnd_2906812 : Nat := 4983230072969 + 3 ^ 40 * 2906812 * 2
def baseEnd_2906812 : Nat := 1492591728257186318381821

theorem tailTrace_2906812 : CollatzResearch.WordTrace tailWord_2906812 prefixEnd_2906812 1492591728257186318381821 := by
  unfold tailWord_2906812
  simp only [CollatzResearch.WordTrace]
  refine ⟨53010071772562021405393345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70680095696749361873857793 53010071772562021405393345)
  ·
    refine ⟨39757553829421516054045009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53010071772562021405393345 39757553829421516054045009)
    ·
      refine ⟨29818165372066137040533757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39757553829421516054045009 29818165372066137040533757)
      ·
        refine ⟨11181812014524801390200159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29818165372066137040533757 11181812014524801390200159)
        ·
          refine ⟨16772718021787202085300239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181812014524801390200159 16772718021787202085300239)
          ·
            refine ⟨25159077032680803127950359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16772718021787202085300239 25159077032680803127950359)
            ·
              refine ⟨37738615549021204691925539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25159077032680803127950359 37738615549021204691925539)
              ·
                refine ⟨56607923323531807037888309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37738615549021204691925539 56607923323531807037888309)
                ·
                  refine ⟨5306992811581106909802029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56607923323531807037888309 5306992811581106909802029)
                  ·
                    refine ⟨1990122304342915091175761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5306992811581106909802029 1990122304342915091175761)
                    ·
                      refine ⟨1492591728257186318381821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990122304342915091175761 1492591728257186318381821)
                      ·
                        rfl

theorem cell23_2906812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2906812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906812 prefixEnd_2906812 := by exact prefixLift 2906812
  have htrace : WordTrace (prefixWord ++ tailWord_2906812) baseStart_2906812 baseEnd_2906812 := by
    simpa [prefixWord, tailWord_2906812, baseEnd_2906812] using wordTrace_append hprefix tailTrace_2906812
  have hstable : (prefixWord ++ tailWord_2906812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906812).length < 2 ^ (prefixWord ++ tailWord_2906812).sum := by decide
  have hdescent : baseEnd_2906812 < baseStart_2906812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906842 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_2906842 : Nat := 118140960795 + 2906842 * 2 ^ 59
def prefixEnd_2906842 : Nat := 4983230072969 + 3 ^ 40 * 2906842 * 2
def baseEnd_2906842 : Nat := 1492607132676821201006683

theorem tailTrace_2906842 : CollatzResearch.WordTrace tailWord_2906842 prefixEnd_2906842 1492607132676821201006683 := by
  unfold tailWord_2906842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505309433753839483594695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70680825156676905289585853 26505309433753839483594695)
  ·
    refine ⟨39757964150630759225392043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26505309433753839483594695 39757964150630759225392043)
    ·
      refine ⟨59636946225946138838088065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39757964150630759225392043 59636946225946138838088065)
      ·
        refine ⟨44727709669459604128566049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59636946225946138838088065 44727709669459604128566049)
        ·
          refine ⟨33545782252094703096424537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44727709669459604128566049 33545782252094703096424537)
          ·
            refine ⟨25159336689071027322318403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33545782252094703096424537 25159336689071027322318403)
            ·
              refine ⟨37739005033606540983477605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25159336689071027322318403 37739005033606540983477605)
              ·
                refine ⟨7076063443801226434402051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37739005033606540983477605 7076063443801226434402051)
                ·
                  refine ⟨10614095165701839651603077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076063443801226434402051 10614095165701839651603077)
                  ·
                    refine ⟨1990142843569094934675577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10614095165701839651603077 1990142843569094934675577)
                    ·
                      refine ⟨1492607132676821201006683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990142843569094934675577 1492607132676821201006683)
                      ·
                        rfl

theorem cell23_2906842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_2906842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906842 prefixEnd_2906842 := by exact prefixLift 2906842
  have htrace : WordTrace (prefixWord ++ tailWord_2906842) baseStart_2906842 baseEnd_2906842 := by
    simpa [prefixWord, tailWord_2906842, baseEnd_2906842] using wordTrace_append hprefix tailTrace_2906842
  have hstable : (prefixWord ++ tailWord_2906842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906842).length < 2 ^ (prefixWord ++ tailWord_2906842).sum := by decide
  have hdescent : baseEnd_2906842 < baseStart_2906842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906848 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 11]
def baseStart_2906848 : Nat := 118140960795 + 2906848 * 2 ^ 59
def prefixEnd_2906848 : Nat := 4983230072969 + 3 ^ 40 * 2906848 * 2
def baseEnd_2906848 : Nat := 165845579284527575281295

theorem tailTrace_2906848 : CollatzResearch.WordTrace tailWord_2906848 prefixEnd_2906848 165845579284527575281295 := by
  unfold tailWord_2906848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53010728286496810479548599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70680971048662413972731465 53010728286496810479548599)
  ·
    refine ⟨79516092429745215719322899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53010728286496810479548599 79516092429745215719322899)
    ·
      refine ⟨119274138644617823578984349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79516092429745215719322899 119274138644617823578984349)
      ·
        refine ⟨44727801991731683842119131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119274138644617823578984349 44727801991731683842119131)
        ·
          refine ⟨67091702987597525763178697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44727801991731683842119131 67091702987597525763178697)
          ·
            refine ⟨50318777240698144322384023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67091702987597525763178697 50318777240698144322384023)
            ·
              refine ⟨75478165861047216483576035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50318777240698144322384023 75478165861047216483576035)
              ·
                refine ⟨113217248791570824725364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75478165861047216483576035 113217248791570824725364053)
                ·
                  refine ⟨165845579284527575281295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 113217248791570824725364053 165845579284527575281295)
                  ·
                    rfl

theorem cell23_2906848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_2906848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906848 prefixEnd_2906848 := by exact prefixLift 2906848
  have htrace : WordTrace (prefixWord ++ tailWord_2906848) baseStart_2906848 baseEnd_2906848 := by
    simpa [prefixWord, tailWord_2906848, baseEnd_2906848] using wordTrace_append hprefix tailTrace_2906848
  have hstable : (prefixWord ++ tailWord_2906848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906848).length < 2 ^ (prefixWord ++ tailWord_2906848).sum := by decide
  have hdescent : baseEnd_2906848 < baseStart_2906848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906865 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 7]
def baseStart_2906865 : Nat := 118140960795 + 2906865 * 2 ^ 59
def prefixEnd_2906865 : Nat := 4983230072969 + 3 ^ 40 * 2906865 * 2
def baseEnd_2906865 : Nat := 165846549192430512335453

theorem tailTrace_2906865 : CollatzResearch.WordTrace tailWord_2906865 prefixEnd_2906865 165846549192430512335453 := by
  unfold tailWord_2906865
  simp only [CollatzResearch.WordTrace]
  refine ⟨106022076613932032862466049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70681384409288021908310699 106022076613932032862466049)
  ·
    refine ⟨79516557460449024646849537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106022076613932032862466049 79516557460449024646849537)
    ·
      refine ⟨59637418095336768485137153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79516557460449024646849537 59637418095336768485137153)
      ·
        refine ⟨44728063571502576363852865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59637418095336768485137153 44728063571502576363852865)
        ·
          refine ⟨33546047678626932272889649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44728063571502576363852865 33546047678626932272889649)
          ·
            refine ⟨25159535758970199204667237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33546047678626932272889649 25159535758970199204667237)
            ·
              refine ⟨4717412954806912350875107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25159535758970199204667237 4717412954806912350875107)
              ·
                refine ⟨7076119432210368526312661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717412954806912350875107 7076119432210368526312661)
                ·
                  refine ⟨165846549192430512335453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7076119432210368526312661 165846549192430512335453)
                  ·
                    rfl

theorem cell23_2906865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_2906865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906865 prefixEnd_2906865 := by exact prefixLift 2906865
  have htrace : WordTrace (prefixWord ++ tailWord_2906865) baseStart_2906865 baseEnd_2906865 := by
    simpa [prefixWord, tailWord_2906865, baseEnd_2906865] using wordTrace_append hprefix tailTrace_2906865
  have hstable : (prefixWord ++ tailWord_2906865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906865).length < 2 ^ (prefixWord ++ tailWord_2906865).sum := by decide
  have hdescent : baseEnd_2906865 < baseStart_2906865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906882 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2906882 : Nat := 118140960795 + 2906882 * 2 ^ 59
def prefixEnd_2906882 : Nat := 4983230072969 + 3 ^ 40 * 2906882 * 2
def baseEnd_2906882 : Nat := 165847519100333449389611

theorem tailTrace_2906882 : CollatzResearch.WordTrace tailWord_2906882 prefixEnd_2906882 165847519100333449389611 := by
  unfold tailWord_2906882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505674163717611191458725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70681797769913629843889933 26505674163717611191458725)
  ·
    refine ⟨4969813905697052098398511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26505674163717611191458725 4969813905697052098398511)
    ·
      refine ⟨7454720858545578147597767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4969813905697052098398511 7454720858545578147597767)
      ·
        refine ⟨11182081287818367221396651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7454720858545578147597767 11182081287818367221396651)
        ·
          refine ⟨16773121931727550832094977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182081287818367221396651 16773121931727550832094977)
          ·
            refine ⟨12579841448795663124071233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16773121931727550832094977 12579841448795663124071233)
            ·
              refine ⟨9434881086596747343053425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12579841448795663124071233 9434881086596747343053425)
              ·
                refine ⟨7076160814947560507290069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434881086596747343053425 7076160814947560507290069)
                ·
                  refine ⟨165847519100333449389611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7076160814947560507290069 165847519100333449389611)
                  ·
                    rfl

theorem cell23_2906882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2906882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906882 prefixEnd_2906882 := by exact prefixLift 2906882
  have htrace : WordTrace (prefixWord ++ tailWord_2906882) baseStart_2906882 baseEnd_2906882 := by
    simpa [prefixWord, tailWord_2906882, baseEnd_2906882] using wordTrace_append hprefix tailTrace_2906882
  have hstable : (prefixWord ++ tailWord_2906882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906882).length < 2 ^ (prefixWord ++ tailWord_2906882).sum := by decide
  have hdescent : baseEnd_2906882 < baseStart_2906882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906895 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 2, 5]
def baseStart_2906895 : Nat := 118140960795 + 2906895 * 2 ^ 59
def prefixEnd_2906895 : Nat := 4983230072969 + 3 ^ 40 * 2906895 * 2
def baseEnd_2906895 : Nat := 497544782383836497881313

theorem tailTrace_2906895 : CollatzResearch.WordTrace tailWord_2906895 prefixEnd_2906895 497544782383836497881313 := by
  unfold tailWord_2906895
  simp only [CollatzResearch.WordTrace]
  refine ⟨106023170803823347986058139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70682113869215565324038759 106023170803823347986058139)
  ·
    refine ⟨159034756205735021979087209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106023170803823347986058139 159034756205735021979087209)
    ·
      refine ⟨119276067154301266484315407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159034756205735021979087209 119276067154301266484315407)
      ·
        refine ⟨178914100731451899726473111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119276067154301266484315407 178914100731451899726473111)
        ·
          refine ⟨268371151097177849589709667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178914100731451899726473111 268371151097177849589709667)
          ·
            refine ⟨402556726645766774384564501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268371151097177849589709667 402556726645766774384564501)
            ·
              refine ⟨18869846561520317549276461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 402556726645766774384564501 18869846561520317549276461)
              ·
                refine ⟨7076192460570119080978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18869846561520317549276461 7076192460570119080978673)
                ·
                  refine ⟨5307144345427589310734005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076192460570119080978673 5307144345427589310734005)
                  ·
                    refine ⟨497544782383836497881313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307144345427589310734005 497544782383836497881313)
                    ·
                      rfl

theorem cell23_2906895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_2906895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906895 prefixEnd_2906895 := by exact prefixLift 2906895
  have htrace : WordTrace (prefixWord ++ tailWord_2906895) baseStart_2906895 baseEnd_2906895 := by
    simpa [prefixWord, tailWord_2906895, baseEnd_2906895] using wordTrace_append hprefix tailTrace_2906895
  have hstable : (prefixWord ++ tailWord_2906895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906895).length < 2 ^ (prefixWord ++ tailWord_2906895).sum := by decide
  have hdescent : baseEnd_2906895 < baseStart_2906895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906912 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_2906912 : Nat := 118140960795 + 2906912 * 2 ^ 59
def prefixEnd_2906912 : Nat := 4983230072969 + 3 ^ 40 * 2906912 * 2
def baseEnd_2906912 : Nat := 497547692107545309043787

theorem tailTrace_2906912 : CollatzResearch.WordTrace tailWord_2906912 prefixEnd_2906912 497547692107545309043787 := by
  unfold tailWord_2906912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53011895422380879944713495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70682527229841173259617993 53011895422380879944713495)
  ·
    refine ⟨79517843133571319917070243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53011895422380879944713495 79517843133571319917070243)
    ·
      refine ⟨119276764700356979875605365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79517843133571319917070243 119276764700356979875605365)
      ·
        refine ⟨11182196690658466863338003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119276764700356979875605365 11182196690658466863338003)
        ·
          refine ⟨16773295035987700295007005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182196690658466863338003 16773295035987700295007005)
          ·
            refine ⟨6289985638495387610627627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16773295035987700295007005 6289985638495387610627627)
            ·
              refine ⟨9434978457743081415941441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289985638495387610627627 9434978457743081415941441)
              ·
                refine ⟨7076233843307311061956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434978457743081415941441 7076233843307311061956081)
                ·
                  refine ⟨5307175382480483296467061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7076233843307311061956081 5307175382480483296467061)
                  ·
                    refine ⟨497547692107545309043787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307175382480483296467061 497547692107545309043787)
                    ·
                      rfl

theorem cell23_2906912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_2906912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906912 prefixEnd_2906912 := by exact prefixLift 2906912
  have htrace : WordTrace (prefixWord ++ tailWord_2906912) baseStart_2906912 baseEnd_2906912 := by
    simpa [prefixWord, tailWord_2906912, baseEnd_2906912] using wordTrace_append hprefix tailTrace_2906912
  have hstable : (prefixWord ++ tailWord_2906912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906912).length < 2 ^ (prefixWord ++ tailWord_2906912).sum := by decide
  have hdescent : baseEnd_2906912 < baseStart_2906912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906916 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 5]
def baseStart_2906916 : Nat := 118140960795 + 2906916 * 2 ^ 59
def prefixEnd_2906916 : Nat := 4983230072969 + 3 ^ 40 * 2906916 * 2
def baseEnd_2906916 : Nat := 165849458916139323497927

theorem tailTrace_2906916 : CollatzResearch.WordTrace tailWord_2906916 prefixEnd_2906916 165849458916139323497927 := by
  unfold tailWord_2906916
  simp only [CollatzResearch.WordTrace]
  refine ⟨53011968368373634286286301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70682624491164845715048401 53011968368373634286286301)
  ·
    refine ⟨19879488138140112857357363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53011968368373634286286301 19879488138140112857357363)
    ·
      refine ⟨29819232207210169286036045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19879488138140112857357363 29819232207210169286036045)
      ·
        refine ⟨11182212077703813482263517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29819232207210169286036045 11182212077703813482263517)
        ·
          refine ⟨4193329529138930055848819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11182212077703813482263517 4193329529138930055848819)
          ·
            refine ⟨6289994293708395083773229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193329529138930055848819 6289994293708395083773229)
            ·
              refine ⟨2358747860140648156414961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6289994293708395083773229 2358747860140648156414961)
              ·
                refine ⟨1769060895105486117311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358747860140648156414961 1769060895105486117311221)
                ·
                  refine ⟨165849458916139323497927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769060895105486117311221 165849458916139323497927)
                  ·
                    rfl

theorem cell23_2906916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_2906916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906916 prefixEnd_2906916 := by exact prefixLift 2906916
  have htrace : WordTrace (prefixWord ++ tailWord_2906916) baseStart_2906916 baseEnd_2906916 := by
    simpa [prefixWord, tailWord_2906916, baseEnd_2906916] using wordTrace_append hprefix tailTrace_2906916
  have hstable : (prefixWord ++ tailWord_2906916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906916).length < 2 ^ (prefixWord ++ tailWord_2906916).sum := by decide
  have hdescent : baseEnd_2906916 < baseStart_2906916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2906975 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_2906975 : Nat := 118140960795 + 2906975 * 2 ^ 59
def prefixEnd_2906975 : Nat := 4983230072969 + 3 ^ 40 * 2906975 * 2
def baseEnd_2906975 : Nat := 1492675425603869180643571

theorem tailTrace_2906975 : CollatzResearch.WordTrace tailWord_2906975 prefixEnd_2906975 1492675425603869180643571 := by
  unfold tailWord_2906975
  simp only [CollatzResearch.WordTrace]
  refine ⟨106026088643533521648970379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70684059095689014432646919 106026088643533521648970379)
  ·
    refine ⟨159039132965300282473455569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106026088643533521648970379 159039132965300282473455569)
    ·
      refine ⟨119279349723975211855091677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159039132965300282473455569 119279349723975211855091677)
      ·
        refine ⟨44729756146490704445659379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119279349723975211855091677 44729756146490704445659379)
        ·
          refine ⟨67094634219736056668489069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44729756146490704445659379 67094634219736056668489069)
          ·
            refine ⟨25160487832401021250683401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67094634219736056668489069 25160487832401021250683401)
            ·
              refine ⟨18870365874300765938012551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25160487832401021250683401 18870365874300765938012551)
              ·
                refine ⟨28305548811451148907018827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18870365874300765938012551 28305548811451148907018827)
                ·
                  refine ⟨42458323217176723360528241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28305548811451148907018827 42458323217176723360528241)
                  ·
                    refine ⟨31843742412882542520396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42458323217176723360528241 31843742412882542520396181)
                    ·
                      refine ⟨1492675425603869180643571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31843742412882542520396181 1492675425603869180643571)
                      ·
                        rfl

theorem cell23_2906975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_2906975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2906975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2906975 prefixEnd_2906975 := by exact prefixLift 2906975
  have htrace : WordTrace (prefixWord ++ tailWord_2906975) baseStart_2906975 baseEnd_2906975 := by
    simpa [prefixWord, tailWord_2906975, baseEnd_2906975] using wordTrace_append hprefix tailTrace_2906975
  have hstable : (prefixWord ++ tailWord_2906975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2906975).length < 2 ^ (prefixWord ++ tailWord_2906975).sum := by decide
  have hdescent : baseEnd_2906975 < baseStart_2906975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2906975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907002 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_2907002 : Nat := 118140960795 + 2907002 * 2 ^ 59
def prefixEnd_2907002 : Nat := 4983230072969 + 3 ^ 40 * 2907002 * 2
def baseEnd_2907002 : Nat := 497563096527180191668649

theorem tailTrace_2907002 : CollatzResearch.WordTrace tailWord_2907002 prefixEnd_2907002 497563096527180191668649 := by
  unfold tailWord_2907002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26506768353608926315050815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70684715609623803506802173 26506768353608926315050815)
  ·
    refine ⟨39760152530413389472576223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26506768353608926315050815 39760152530413389472576223)
    ·
      refine ⟨59640228795620084208864335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39760152530413389472576223 59640228795620084208864335)
      ·
        refine ⟨89460343193430126313296503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59640228795620084208864335 89460343193430126313296503)
        ·
          refine ⟨134190514790145189469944755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89460343193430126313296503 134190514790145189469944755)
          ·
            refine ⟨201285772185217784204917133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134190514790145189469944755 201285772185217784204917133)
            ·
              refine ⟨75482164569456669076843925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201285772185217784204917133 75482164569456669076843925)
              ·
                refine ⟨3538226464193281362977059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75482164569456669076843925 3538226464193281362977059)
                ·
                  refine ⟨5307339696289922044465589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538226464193281362977059 5307339696289922044465589)
                  ·
                    refine ⟨497563096527180191668649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307339696289922044465589 497563096527180191668649)
                    ·
                      rfl

theorem cell23_2907002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_2907002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907002 prefixEnd_2907002 := by exact prefixLift 2907002
  have htrace : WordTrace (prefixWord ++ tailWord_2907002) baseStart_2907002 baseEnd_2907002 := by
    simpa [prefixWord, tailWord_2907002, baseEnd_2907002] using wordTrace_append hprefix tailTrace_2907002
  have hstable : (prefixWord ++ tailWord_2907002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907002).length < 2 ^ (prefixWord ++ tailWord_2907002).sum := by decide
  have hdescent : baseEnd_2907002 < baseStart_2907002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907019 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 1, 5]
def baseStart_2907019 : Nat := 118140960795 + 2907019 * 2 ^ 59
def prefixEnd_2907019 : Nat := 4983230072969 + 3 ^ 40 * 2907019 * 2
def baseEnd_2907019 : Nat := 497566006250889002831123

theorem tailTrace_2907019 : CollatzResearch.WordTrace tailWord_2907019 prefixEnd_2907019 497566006250889002831123 := by
  unfold tailWord_2907019
  simp only [CollatzResearch.WordTrace]
  refine ⟨106027693455374117163572111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70685128970249411442381407 106027693455374117163572111)
  ·
    refine ⟨159041540183061175745358167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106027693455374117163572111 159041540183061175745358167)
    ·
      refine ⟨238562310274591763618037251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159041540183061175745358167 238562310274591763618037251)
      ·
        refine ⟨357843465411887645427055877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238562310274591763618037251 357843465411887645427055877)
        ·
          refine ⟨67095649764728933517572977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357843465411887645427055877 67095649764728933517572977)
          ·
            refine ⟨50321737323546700138179733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67095649764728933517572977 50321737323546700138179733)
            ·
              refine ⟨2358831437041251568977175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50321737323546700138179733 2358831437041251568977175)
              ·
                refine ⟨3538247155561877353465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358831437041251568977175 3538247155561877353465763)
                ·
                  refine ⟨5307370733342816030198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538247155561877353465763 5307370733342816030198645)
                  ·
                    refine ⟨497566006250889002831123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307370733342816030198645 497566006250889002831123)
                    ·
                      rfl

theorem cell23_2907019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 5].length) (baseStart_2907019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907019 prefixEnd_2907019 := by exact prefixLift 2907019
  have htrace : WordTrace (prefixWord ++ tailWord_2907019) baseStart_2907019 baseEnd_2907019 := by
    simpa [prefixWord, tailWord_2907019, baseEnd_2907019] using wordTrace_append hprefix tailTrace_2907019
  have hstable : (prefixWord ++ tailWord_2907019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907019).length < 2 ^ (prefixWord ++ tailWord_2907019).sum := by decide
  have hdescent : baseEnd_2907019 < baseStart_2907019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907053 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2907053 : Nat := 118140960795 + 2907053 * 2 ^ 59
def prefixEnd_2907053 : Nat := 4983230072969 + 3 ^ 40 * 2907053 * 2
def baseEnd_2907053 : Nat := 497571825698306625156071

theorem tailTrace_2907053 : CollatzResearch.WordTrace tailWord_2907053 prefixEnd_2907053 497571825698306625156071 := by
  unfold tailWord_2907053
  simp only [CollatzResearch.WordTrace]
  refine ⟨106028933537250940970309813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70685955691500627313539875 106028933537250940970309813)
  ·
    refine ⟨9940212519117275715966545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106028933537250940970309813 9940212519117275715966545)
    ·
      refine ⟨7455159389337956786974909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9940212519117275715966545 7455159389337956786974909)
      ·
        refine ⟨2795684771001733795115591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7455159389337956786974909 2795684771001733795115591)
        ·
          refine ⟨4193527156502600692673387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795684771001733795115591 4193527156502600692673387)
          ·
            refine ⟨6290290734753901039010081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193527156502600692673387 6290290734753901039010081)
            ·
              refine ⟨4717718051065425779257561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290290734753901039010081 4717718051065425779257561)
              ·
                refine ⟨3538288538299069334443171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717718051065425779257561 3538288538299069334443171)
                ·
                  refine ⟨5307432807448604001664757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538288538299069334443171 5307432807448604001664757)
                  ·
                    refine ⟨497571825698306625156071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307432807448604001664757 497571825698306625156071)
                    ·
                      rfl

theorem cell23_2907053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2907053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907053 prefixEnd_2907053 := by exact prefixLift 2907053
  have htrace : WordTrace (prefixWord ++ tailWord_2907053) baseStart_2907053 baseEnd_2907053 := by
    simpa [prefixWord, tailWord_2907053, baseEnd_2907053] using wordTrace_append hprefix tailTrace_2907053
  have hstable : (prefixWord ++ tailWord_2907053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907053).length < 2 ^ (prefixWord ++ tailWord_2907053).sum := by decide
  have hdescent : baseEnd_2907053 < baseStart_2907053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907089 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_2907089 : Nat := 118140960795 + 2907089 * 2 ^ 59
def prefixEnd_2907089 : Nat := 4983230072969 + 3 ^ 40 * 2907089 * 2
def baseEnd_2907089 : Nat := 1492733962398481734618047

theorem tailTrace_2907089 : CollatzResearch.WordTrace tailWord_2907089 prefixEnd_2907089 1492733962398481734618047 := by
  unfold tailWord_2907089
  simp only [CollatzResearch.WordTrace]
  refine ⟨106030246565120519118620321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70686831043413679412413547 106030246565120519118620321)
  ·
    refine ⟨79522684923840389338965241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106030246565120519118620321 79522684923840389338965241)
    ·
      refine ⟨59642013692880292004223931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79522684923840389338965241 59642013692880292004223931)
      ·
        refine ⟨89463020539320438006335897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59642013692880292004223931 89463020539320438006335897)
        ·
          refine ⟨67097265404490328504751923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89463020539320438006335897 67097265404490328504751923)
          ·
            refine ⟨100645898106735492757127885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67097265404490328504751923 100645898106735492757127885)
            ·
              refine ⟨37742211790025809783922957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100645898106735492757127885 37742211790025809783922957)
              ·
                refine ⟨14153329421259678668971109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37742211790025809783922957 14153329421259678668971109)
                ·
                  refine ⟨2653749266486189750432083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14153329421259678668971109 2653749266486189750432083)
                  ·
                    refine ⟨3980623899729284625648125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2653749266486189750432083 3980623899729284625648125)
                    ·
                      refine ⟨1492733962398481734618047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3980623899729284625648125 1492733962398481734618047)
                      ·
                        rfl

theorem cell23_2907089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_2907089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907089 prefixEnd_2907089 := by exact prefixLift 2907089
  have htrace : WordTrace (prefixWord ++ tailWord_2907089) baseStart_2907089 baseEnd_2907089 := by
    simpa [prefixWord, tailWord_2907089, baseEnd_2907089] using wordTrace_append hprefix tailTrace_2907089
  have hstable : (prefixWord ++ tailWord_2907089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907089).length < 2 ^ (prefixWord ++ tailWord_2907089).sum := by decide
  have hdescent : baseEnd_2907089 < baseStart_2907089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907090 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2907090 : Nat := 118140960795 + 2907090 * 2 ^ 59
def prefixEnd_2907090 : Nat := 4983230072969 + 3 ^ 40 * 2907090 * 2
def baseEnd_2907090 : Nat := 1492734475879136230705543

theorem tailTrace_2907090 : CollatzResearch.WordTrace tailWord_2907090 prefixEnd_2907090 1492734475879136230705543 := by
  unfold tailWord_2907090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507570759529224072351681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70686855358744597526271149 26507570759529224072351681)
  ·
    refine ⟨19880678069646918054263761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26507570759529224072351681 19880678069646918054263761)
    ·
      refine ⟨14910508552235188540697821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19880678069646918054263761 14910508552235188540697821)
      ·
        refine ⟨5591440707088195702761683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14910508552235188540697821 5591440707088195702761683)
        ·
          refine ⟨8387161060632293554142525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591440707088195702761683 8387161060632293554142525)
          ·
            refine ⟨3145185397737110082803447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8387161060632293554142525 3145185397737110082803447)
            ·
              refine ⟨4717778096605665124205171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145185397737110082803447 4717778096605665124205171)
              ·
                refine ⟨7076667144908497686307757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717778096605665124205171 7076667144908497686307757)
                ·
                  refine ⟨2653750179340686632365409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7076667144908497686307757 2653750179340686632365409)
                  ·
                    refine ⟨1990312634505514974274057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653750179340686632365409 1990312634505514974274057)
                    ·
                      refine ⟨1492734475879136230705543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990312634505514974274057 1492734475879136230705543)
                      ·
                        rfl

theorem cell23_2907090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2907090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907090 prefixEnd_2907090 := by exact prefixLift 2907090
  have htrace : WordTrace (prefixWord ++ tailWord_2907090) baseStart_2907090 baseEnd_2907090 := by
    simpa [prefixWord, tailWord_2907090, baseEnd_2907090] using wordTrace_append hprefix tailTrace_2907090
  have hstable : (prefixWord ++ tailWord_2907090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907090).length < 2 ^ (prefixWord ++ tailWord_2907090).sum := by decide
  have hdescent : baseEnd_2907090 < baseStart_2907090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907124 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2907124 : Nat := 118140960795 + 2907124 * 2 ^ 59
def prefixEnd_2907124 : Nat := 4983230072969 + 3 ^ 40 * 2907124 * 2
def baseEnd_2907124 : Nat := 1492751934221389097680387

theorem tailTrace_2907124 : CollatzResearch.WordTrace tailWord_2907124 prefixEnd_2907124 1492751934221389097680387 := by
  unfold tailWord_2907124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53015761559996860048072213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70687682079995813397429617 53015761559996860048072213)
  ·
    refine ⟨2485113823124852814753385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53015761559996860048072213 2485113823124852814753385)
    ·
      refine ⟨1863835367343639611065039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485113823124852814753385 1863835367343639611065039)
      ·
        refine ⟨2795753051015459416597559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863835367343639611065039 2795753051015459416597559)
        ·
          refine ⟨4193629576523189124896339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795753051015459416597559 4193629576523189124896339)
          ·
            refine ⟨6290444364784783687344509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193629576523189124896339 6290444364784783687344509)
            ·
              refine ⟨2358916636794293882754191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290444364784783687344509 2358916636794293882754191)
              ·
                refine ⟨3538374955191440824131287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358916636794293882754191 3538374955191440824131287)
                ·
                  refine ⟨5307562432787161236196931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538374955191440824131287 5307562432787161236196931)
                  ·
                    refine ⟨7961343649180741854295397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5307562432787161236196931 7961343649180741854295397)
                    ·
                      refine ⟨1492751934221389097680387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7961343649180741854295397 1492751934221389097680387)
                      ·
                        rfl

theorem cell23_2907124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2907124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907124 prefixEnd_2907124 := by exact prefixLift 2907124
  have htrace : WordTrace (prefixWord ++ tailWord_2907124) baseStart_2907124 baseEnd_2907124 := by
    simpa [prefixWord, tailWord_2907124, baseEnd_2907124] using wordTrace_append hprefix tailTrace_2907124
  have hstable : (prefixWord ++ tailWord_2907124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907124).length < 2 ^ (prefixWord ++ tailWord_2907124).sum := by decide
  have hdescent : baseEnd_2907124 < baseStart_2907124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907159 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2907159 : Nat := 118140960795 + 2907159 * 2 ^ 59
def prefixEnd_2907159 : Nat := 4983230072969 + 3 ^ 40 * 2907159 * 2
def baseEnd_2907159 : Nat := 1492769906044296460742725

theorem tailTrace_2907159 : CollatzResearch.WordTrace tailWord_2907159 prefixEnd_2907159 1492769906044296460742725 := by
  unfold tailWord_2907159
  simp only [CollatzResearch.WordTrace]
  refine ⟨106032799674866921073668531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70688533116577947382445687 106032799674866921073668531)
  ·
    refine ⟨159049199512300381610502797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106032799674866921073668531 159049199512300381610502797)
    ·
      refine ⟨59643449817112643103938549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159049199512300381610502797 59643449817112643103938549)
      ·
        refine ⟨5591573420354310290994239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59643449817112643103938549 5591573420354310290994239)
        ·
          refine ⟨8387360130531465436491359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591573420354310290994239 8387360130531465436491359)
          ·
            refine ⟨12581040195797198154737039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8387360130531465436491359 12581040195797198154737039)
            ·
              refine ⟨18871560293695797232105559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12581040195797198154737039 18871560293695797232105559)
              ·
                refine ⟨28307340440543695848158339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18871560293695797232105559 28307340440543695848158339)
                ·
                  refine ⟨42461010660815543772237509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28307340440543695848158339 42461010660815543772237509)
                  ·
                    refine ⟨7961439498902914457294533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42461010660815543772237509 7961439498902914457294533)
                    ·
                      refine ⟨1492769906044296460742725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7961439498902914457294533 1492769906044296460742725)
                      ·
                        rfl

theorem cell23_2907159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2907159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907159 prefixEnd_2907159 := by exact prefixLift 2907159
  have htrace : WordTrace (prefixWord ++ tailWord_2907159) baseStart_2907159 baseEnd_2907159 := by
    simpa [prefixWord, tailWord_2907159, baseEnd_2907159] using wordTrace_append hprefix tailTrace_2907159
  have hstable : (prefixWord ++ tailWord_2907159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907159).length < 2 ^ (prefixWord ++ tailWord_2907159).sum := by decide
  have hdescent : baseEnd_2907159 < baseStart_2907159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907169 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 7]
def baseStart_2907169 : Nat := 118140960795 + 2907169 * 2 ^ 59
def prefixEnd_2907169 : Nat := 4983230072969 + 3 ^ 40 * 2907169 * 2
def baseEnd_2907169 : Nat := 165863893427871269068631

theorem tailTrace_2907169 : CollatzResearch.WordTrace tailWord_2907169 prefixEnd_2907169 165863893427871269068631 := by
  unfold tailWord_2907169
  simp only [CollatzResearch.WordTrace]
  refine ⟨106033164404830692781532561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70688776269887128521021707 106033164404830692781532561)
  ·
    refine ⟨79524873303623019586149421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106033164404830692781532561 79524873303623019586149421)
    ·
      refine ⟨29821827488858632344806033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79524873303623019586149421 29821827488858632344806033)
      ·
        refine ⟨22366370616643974258604525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29821827488858632344806033 22366370616643974258604525)
        ·
          refine ⟨8387388981241490346976697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22366370616643974258604525 8387388981241490346976697)
          ·
            refine ⟨6290541735931117760232523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8387388981241490346976697 6290541735931117760232523)
            ·
              refine ⟨9435812603896676640348785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290541735931117760232523 9435812603896676640348785)
              ·
                refine ⟨7076859452922507480261589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9435812603896676640348785 7076859452922507480261589)
                ·
                  refine ⟨165863893427871269068631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7076859452922507480261589 165863893427871269068631)
                  ·
                    rfl

theorem cell23_2907169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_2907169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907169 prefixEnd_2907169 := by exact prefixLift 2907169
  have htrace : WordTrace (prefixWord ++ tailWord_2907169) baseStart_2907169 baseEnd_2907169 := by
    simpa [prefixWord, tailWord_2907169, baseEnd_2907169] using wordTrace_append hprefix tailTrace_2907169
  have hstable : (prefixWord ++ tailWord_2907169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907169).length < 2 ^ (prefixWord ++ tailWord_2907169).sum := by decide
  have hdescent : baseEnd_2907169 < baseStart_2907169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907186 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_2907186 : Nat := 118140960795 + 2907186 * 2 ^ 59
def prefixEnd_2907186 : Nat := 4983230072969 + 3 ^ 40 * 2907186 * 2
def baseEnd_2907186 : Nat := 165864863335774206122789

theorem tailTrace_2907186 : CollatzResearch.WordTrace tailWord_2907186 prefixEnd_2907186 165864863335774206122789 := by
  unfold tailWord_2907186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26508446111442276171225353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70689189630512736456600941 26508446111442276171225353)
  ·
    refine ⟨19881334583581707128419015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26508446111442276171225353 19881334583581707128419015)
    ·
      refine ⟨29822001875372560692628523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881334583581707128419015 29822001875372560692628523)
      ·
        refine ⟨44733002813058841038942785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29822001875372560692628523 44733002813058841038942785)
        ·
          refine ⟨33549752109794130779207089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44733002813058841038942785 33549752109794130779207089)
          ·
            refine ⟨25162314082345598084405317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33549752109794130779207089 25162314082345598084405317)
            ·
              refine ⟨4717933890439799640825997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25162314082345598084405317 4717933890439799640825997)
              ·
                refine ⟨1769225208914924865309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4717933890439799640825997 1769225208914924865309749)
                ·
                  refine ⟨165864863335774206122789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769225208914924865309749 165864863335774206122789)
                  ·
                    rfl

theorem cell23_2907186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_2907186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907186 prefixEnd_2907186 := by exact prefixLift 2907186
  have htrace : WordTrace (prefixWord ++ tailWord_2907186) baseStart_2907186 baseEnd_2907186 := by
    simpa [prefixWord, tailWord_2907186, baseEnd_2907186] using wordTrace_append hprefix tailTrace_2907186
  have hstable : (prefixWord ++ tailWord_2907186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907186).length < 2 ^ (prefixWord ++ tailWord_2907186).sum := by decide
  have hdescent : baseEnd_2907186 < baseStart_2907186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907319 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 6]
def baseStart_2907319 : Nat := 118140960795 + 2907319 * 2 ^ 59
def prefixEnd_2907319 : Nat := 4983230072969 + 3 ^ 40 * 2907319 * 2
def baseEnd_2907319 : Nat := 497617354316338611580663

theorem tailTrace_2907319 : CollatzResearch.WordTrace tailWord_2907319 prefixEnd_2907319 497617354316338611580663 := by
  unfold tailWord_2907319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106038635354287268399493011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70692423569524845599662007 106038635354287268399493011)
  ·
    refine ⟨159057953031430902599239517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106038635354287268399493011 159057953031430902599239517)
    ·
      refine ⟨59646732386786588474714819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159057953031430902599239517 59646732386786588474714819)
      ·
        refine ⟨89470098580179882712072229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59646732386786588474714819 89470098580179882712072229)
        ·
          refine ⟨16775643483783728008513543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89470098580179882712072229 16775643483783728008513543)
          ·
            refine ⟨25163465225675592012770315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16775643483783728008513543 25163465225675592012770315)
            ·
              refine ⟨37745197838513388019155473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25163465225675592012770315 37745197838513388019155473)
              ·
                refine ⟨28308898378885041014366605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37745197838513388019155473 28308898378885041014366605)
                ·
                  refine ⟨10615836892081890380387477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28308898378885041014366605 10615836892081890380387477)
                  ·
                    refine ⟨497617354316338611580663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10615836892081890380387477 497617354316338611580663)
                    ·
                      rfl

theorem cell23_2907319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_2907319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907319 prefixEnd_2907319 := by exact prefixLift 2907319
  have htrace : WordTrace (prefixWord ++ tailWord_2907319) baseStart_2907319 baseEnd_2907319 := by
    simpa [prefixWord, tailWord_2907319, baseEnd_2907319] using wordTrace_append hprefix tailTrace_2907319
  have hstable : (prefixWord ++ tailWord_2907319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907319).length < 2 ^ (prefixWord ++ tailWord_2907319).sum := by decide
  have hdescent : baseEnd_2907319 < baseStart_2907319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907357 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2907357 : Nat := 118140960795 + 2907357 * 2 ^ 59
def prefixEnd_2907357 : Nat := 4983230072969 + 3 ^ 40 * 2907357 * 2
def baseEnd_2907357 : Nat := 497623858404628895355605

theorem tailTrace_2907357 : CollatzResearch.WordTrace tailWord_2907357 prefixEnd_2907357 497623858404628895355605 := by
  unfold tailWord_2907357
  simp only [CollatzResearch.WordTrace]
  refine ⟨106040021328149600889376325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70693347552099733926250883 106040021328149600889376325)
  ·
    refine ⟨19882503999028050166758061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106040021328149600889376325 19882503999028050166758061)
    ·
      refine ⟨7455938999635518812534273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19882503999028050166758061 7455938999635518812534273)
      ·
        refine ⟨5591954249726639109400705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455938999635518812534273 5591954249726639109400705)
        ·
          refine ⟨4193965687294979332050529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5591954249726639109400705 4193965687294979332050529)
          ·
            refine ⟨3145474265471234499037897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193965687294979332050529 3145474265471234499037897)
            ·
              refine ⟨2359105699103425874278423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145474265471234499037897 2359105699103425874278423)
              ·
                refine ⟨3538658548655138811417635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359105699103425874278423 3538658548655138811417635)
                ·
                  refine ⟨5307987822982708217126453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538658548655138811417635 5307987822982708217126453)
                  ·
                    refine ⟨497623858404628895355605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5307987822982708217126453 497623858404628895355605)
                    ·
                      rfl

theorem cell23_2907357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2907357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907357 prefixEnd_2907357 := by exact prefixLift 2907357
  have htrace : WordTrace (prefixWord ++ tailWord_2907357) baseStart_2907357 baseEnd_2907357 := by
    simpa [prefixWord, tailWord_2907357, baseEnd_2907357] using wordTrace_append hprefix tailTrace_2907357
  have hstable : (prefixWord ++ tailWord_2907357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907357).length < 2 ^ (prefixWord ++ tailWord_2907357).sum := by decide
  have hdescent : baseEnd_2907357 < baseStart_2907357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907360 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4]
def baseStart_2907360 : Nat := 118140960795 + 2907360 * 2 ^ 59
def prefixEnd_2907360 : Nat := 4983230072969 + 3 ^ 40 * 2907360 * 2
def baseEnd_2907360 : Nat := 1492873115655850174329301

theorem tailTrace_2907360 : CollatzResearch.WordTrace tailWord_2907360 prefixEnd_2907360 1492873115655850174329301 := by
  unfold tailWord_2907360
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020065373569366200867767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70693420498092488267823689 53020065373569366200867767)
  ·
    refine ⟨79530098060354049301301651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53020065373569366200867767 79530098060354049301301651)
    ·
      refine ⟨119295147090531073951952477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79530098060354049301301651 119295147090531073951952477)
      ·
        refine ⟨44735680158949152731982179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119295147090531073951952477 44735680158949152731982179)
        ·
          refine ⟨67103520238423729097973269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44735680158949152731982179 67103520238423729097973269)
          ·
            refine ⟨3145477511176112301467497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67103520238423729097973269 3145477511176112301467497)
            ·
              refine ⟨2359108133382084226100623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145477511176112301467497 2359108133382084226100623)
              ·
                refine ⟨3538662200073126339150935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359108133382084226100623 3538662200073126339150935)
                ·
                  refine ⟨5307993300109689508726403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538662200073126339150935 5307993300109689508726403)
                  ·
                    refine ⟨7961989950164534263089605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5307993300109689508726403 7961989950164534263089605)
                    ·
                      refine ⟨1492873115655850174329301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7961989950164534263089605 1492873115655850174329301)
                      ·
                        rfl

theorem cell23_2907360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_2907360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907360 prefixEnd_2907360 := by exact prefixLift 2907360
  have htrace : WordTrace (prefixWord ++ tailWord_2907360) baseStart_2907360 baseEnd_2907360 := by
    simpa [prefixWord, tailWord_2907360, baseEnd_2907360] using wordTrace_append hprefix tailTrace_2907360
  have hstable : (prefixWord ++ tailWord_2907360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907360).length < 2 ^ (prefixWord ++ tailWord_2907360).sum := by decide
  have hdescent : baseEnd_2907360 < baseStart_2907360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907370 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2907370 : Nat := 118140960795 + 2907370 * 2 ^ 59
def prefixEnd_2907370 : Nat := 4983230072969 + 3 ^ 40 * 2907370 * 2
def baseEnd_2907370 : Nat := 497626083487465045068085

theorem tailTrace_2907370 : CollatzResearch.WordTrace tailWord_2907370 prefixEnd_2907370 497626083487465045068085 := by
  unfold tailWord_2907370
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510123869275626027399891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70693663651401669406399709 26510123869275626027399891)
  ·
    refine ⟨39765185803913439041099837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26510123869275626027399891 39765185803913439041099837)
    ·
      refine ⟨14911944676467539640412439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39765185803913439041099837 14911944676467539640412439)
      ·
        refine ⟨22367917014701309460618659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911944676467539640412439 22367917014701309460618659)
        ·
          refine ⟨33551875522051964190927989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22367917014701309460618659 33551875522051964190927989)
          ·
            refine ⟨3145488330192371642899499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33551875522051964190927989 3145488330192371642899499)
            ·
              refine ⟨4718232495288557464349249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145488330192371642899499 4718232495288557464349249)
              ·
                refine ⟨3538674371466418098261937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718232495288557464349249 3538674371466418098261937)
                ·
                  refine ⟨2654005778599813573696453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538674371466418098261937 2654005778599813573696453)
                  ·
                    refine ⟨497626083487465045068085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654005778599813573696453 497626083487465045068085)
                    ·
                      rfl

theorem cell23_2907370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2907370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907370 prefixEnd_2907370 := by exact prefixLift 2907370
  have htrace : WordTrace (prefixWord ++ tailWord_2907370) baseStart_2907370 baseEnd_2907370 := by
    simpa [prefixWord, tailWord_2907370, baseEnd_2907370] using wordTrace_append hprefix tailTrace_2907370
  have hstable : (prefixWord ++ tailWord_2907370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907370).length < 2 ^ (prefixWord ++ tailWord_2907370).sum := by decide
  have hdescent : baseEnd_2907370 < baseStart_2907370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907390 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2907390 : Nat := 118140960795 + 2907390 * 2 ^ 59
def prefixEnd_2907390 : Nat := 4983230072969 + 3 ^ 40 * 2907390 * 2
def baseEnd_2907390 : Nat := 1492888520075485056954163

theorem tailTrace_2907390 : CollatzResearch.WordTrace tailWord_2907390 prefixEnd_2907390 1492888520075485056954163 := by
  unfold tailWord_2907390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255153117128755940665953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70694149958020031683551749 13255153117128755940665953)
  ·
    refine ⟨9941364837846566955499465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13255153117128755940665953 9941364837846566955499465)
    ·
      refine ⟨7456023628384925216624599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9941364837846566955499465 7456023628384925216624599)
      ·
        refine ⟨11184035442577387824936899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456023628384925216624599 11184035442577387824936899)
        ·
          refine ⟨16776053163866081737405349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11184035442577387824936899 16776053163866081737405349)
          ·
            refine ⟨3145509968224890325763503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16776053163866081737405349 3145509968224890325763503)
            ·
              refine ⟨4718264952337335488645255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145509968224890325763503 4718264952337335488645255)
              ·
                refine ⟨7077397428506003232967883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718264952337335488645255 7077397428506003232967883)
                ·
                  refine ⟨10616096142759004849451825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7077397428506003232967883 10616096142759004849451825)
                  ·
                    refine ⟨7962072107069253637088869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10616096142759004849451825 7962072107069253637088869)
                    ·
                      refine ⟨1492888520075485056954163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7962072107069253637088869 1492888520075485056954163)
                      ·
                        rfl

theorem cell23_2907390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2907390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907390 prefixEnd_2907390 := by exact prefixLift 2907390
  have htrace : WordTrace (prefixWord ++ tailWord_2907390) baseStart_2907390 baseEnd_2907390 := by
    simpa [prefixWord, tailWord_2907390, baseEnd_2907390] using wordTrace_append hprefix tailTrace_2907390
  have hstable : (prefixWord ++ tailWord_2907390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907390).length < 2 ^ (prefixWord ++ tailWord_2907390).sum := by decide
  have hdescent : baseEnd_2907390 < baseStart_2907390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907393 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2907393 : Nat := 118140960795 + 2907393 * 2 ^ 59
def prefixEnd_2907393 : Nat := 4983230072969 + 3 ^ 40 * 2907393 * 2
def baseEnd_2907393 : Nat := 1492890060517448545216649

theorem tailTrace_2907393 : CollatzResearch.WordTrace tailWord_2907393 prefixEnd_2907393 1492890060517448545216649 := by
  unfold tailWord_2907393
  simp only [CollatzResearch.WordTrace]
  refine ⟨106041334356019179037686833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70694222904012786025124555 106041334356019179037686833)
  ·
    refine ⟨79531000767014384278265125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106041334356019179037686833 79531000767014384278265125)
    ·
      refine ⟨14912062643815197052174711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79531000767014384278265125 14912062643815197052174711)
      ·
        refine ⟨22368093965722795578262067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912062643815197052174711 22368093965722795578262067)
        ·
          refine ⟨33552140948584193367393101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368093965722795578262067 33552140948584193367393101)
          ·
            refine ⟨12582052855719072512772413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33552140948584193367393101 12582052855719072512772413)
            ·
              refine ⟨4718269820894652192289655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12582052855719072512772413 4718269820894652192289655)
              ·
                refine ⟨7077404731341978288434483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718269820894652192289655 7077404731341978288434483)
                ·
                  refine ⟨10616107097012967432651725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7077404731341978288434483 10616107097012967432651725)
                  ·
                    refine ⟨3981040161379862787244397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10616107097012967432651725 3981040161379862787244397)
                    ·
                      refine ⟨1492890060517448545216649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981040161379862787244397 1492890060517448545216649)
                      ·
                        rfl

theorem cell23_2907393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2907393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907393 prefixEnd_2907393 := by exact prefixLift 2907393
  have htrace : WordTrace (prefixWord ++ tailWord_2907393) baseStart_2907393 baseEnd_2907393 := by
    simpa [prefixWord, tailWord_2907393, baseEnd_2907393] using wordTrace_append hprefix tailTrace_2907393
  have hstable : (prefixWord ++ tailWord_2907393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907393).length < 2 ^ (prefixWord ++ tailWord_2907393).sum := by decide
  have hdescent : baseEnd_2907393 < baseStart_2907393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907400 : List Nat := [2, 1, 3, 2, 5, 1, 2, 7]
def baseStart_2907400 : Nat := 118140960795 + 2907400 * 2 ^ 59
def prefixEnd_2907400 : Nat := 4983230072969 + 3 ^ 40 * 2907400 * 2
def baseEnd_2907400 : Nat := 55292357588223333993671

theorem tailTrace_2907400 : CollatzResearch.WordTrace tailWord_2907400 prefixEnd_2907400 55292357588223333993671 := by
  unfold tailWord_2907400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020794833496909616595827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70694393111329212822127769 53020794833496909616595827)
  ·
    refine ⟨79531192250245364424893741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53020794833496909616595827 79531192250245364424893741)
    ·
      refine ⟨29824197093842011659335153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79531192250245364424893741 29824197093842011659335153)
      ·
        refine ⟨22368147820381508744501365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29824197093842011659335153 22368147820381508744501365)
        ·
          refine ⟨2097013858160766444797003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22368147820381508744501365 2097013858160766444797003)
          ·
            refine ⟨3145520787241149667195505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097013858160766444797003 3145520787241149667195505)
            ·
              refine ⟨2359140590430862250396629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145520787241149667195505 2359140590430862250396629)
              ·
                refine ⟨55292357588223333993671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2359140590430862250396629 55292357588223333993671)
                ·
                  rfl

theorem cell23_2907400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 7].length) (baseStart_2907400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907400 prefixEnd_2907400 := by exact prefixLift 2907400
  have htrace : WordTrace (prefixWord ++ tailWord_2907400) baseStart_2907400 baseEnd_2907400 := by
    simpa [prefixWord, tailWord_2907400, baseEnd_2907400] using wordTrace_append hprefix tailTrace_2907400
  have hstable : (prefixWord ++ tailWord_2907400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907400).length < 2 ^ (prefixWord ++ tailWord_2907400).sum := by decide
  have hdescent : baseEnd_2907400 < baseStart_2907400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907406 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2907406 : Nat := 118140960795 + 2907406 * 2 ^ 59
def prefixEnd_2907406 : Nat := 4983230072969 + 3 ^ 40 * 2907406 * 2
def baseEnd_2907406 : Nat := 1492896735765956994354089

theorem tailTrace_2907406 : CollatzResearch.WordTrace tailWord_2907406 prefixEnd_2907406 1492896735765956994354089 := by
  unfold tailWord_2907406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255226063121510282238759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70694539003314721505273381 13255226063121510282238759)
  ·
    refine ⟨19882839094682265423358139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13255226063121510282238759 19882839094682265423358139)
    ·
      refine ⟨29824258642023398135037209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19882839094682265423358139 29824258642023398135037209)
      ·
        refine ⟨22368193981517548601277907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29824258642023398135037209 22368193981517548601277907)
        ·
          refine ⟨33552290972276322901916861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368193981517548601277907 33552290972276322901916861)
          ·
            refine ⟨12582109114603621088218823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33552290972276322901916861 12582109114603621088218823)
            ·
              refine ⟨18873163671905431632328235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12582109114603621088218823 18873163671905431632328235)
              ·
                refine ⟨28309745507858147448492353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18873163671905431632328235 28309745507858147448492353)
                ·
                  refine ⟨21232309130893610586369265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28309745507858147448492353 21232309130893610586369265)
                  ·
                    refine ⟨15924231848170207939776949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21232309130893610586369265 15924231848170207939776949)
                    ·
                      refine ⟨1492896735765956994354089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15924231848170207939776949 1492896735765956994354089)
                      ·
                        rfl

theorem cell23_2907406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2907406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907406 prefixEnd_2907406 := by exact prefixLift 2907406
  have htrace : WordTrace (prefixWord ++ tailWord_2907406) baseStart_2907406 baseEnd_2907406 := by
    simpa [prefixWord, tailWord_2907406, baseEnd_2907406] using wordTrace_append hprefix tailTrace_2907406
  have hstable : (prefixWord ++ tailWord_2907406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907406).length < 2 ^ (prefixWord ++ tailWord_2907406).sum := by decide
  have hdescent : baseEnd_2907406 < baseStart_2907406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907420 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2907420 : Nat := 118140960795 + 2907420 * 2 ^ 59
def prefixEnd_2907420 : Nat := 4983230072969 + 3 ^ 40 * 2907420 * 2
def baseEnd_2907420 : Nat := 1492903924495119939579025

theorem tailTrace_2907420 : CollatzResearch.WordTrace tailWord_2907420 prefixEnd_2907420 1492903924495119939579025 := by
  unfold tailWord_2907420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53021159563460681324459857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70694879417947575099279809 53021159563460681324459857)
  ·
    refine ⟨39765869672595510993344893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53021159563460681324459857 39765869672595510993344893)
    ·
      refine ⟨14912201127223316622504335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39765869672595510993344893 14912201127223316622504335)
      ·
        refine ⟨22368301690834974933756503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912201127223316622504335 22368301690834974933756503)
        ·
          refine ⟨33552452536252462400634755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368301690834974933756503 33552452536252462400634755)
          ·
            refine ⟨50328678804378693600952133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33552452536252462400634755 50328678804378693600952133)
            ·
              refine ⟨9436627275821005050178525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50328678804378693600952133 9436627275821005050178525)
              ·
                refine ⟨3538735228432876893816947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9436627275821005050178525 3538735228432876893816947)
                ·
                  refine ⟨5308102842649315340725421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538735228432876893816947 5308102842649315340725421)
                  ·
                    refine ⟨1990538565993493252772033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5308102842649315340725421 1990538565993493252772033)
                    ·
                      refine ⟨1492903924495119939579025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990538565993493252772033 1492903924495119939579025)
                      ·
                        rfl

theorem cell23_2907420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2907420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907420 prefixEnd_2907420 := by exact prefixLift 2907420
  have htrace : WordTrace (prefixWord ++ tailWord_2907420) baseStart_2907420 baseEnd_2907420 := by
    simpa [prefixWord, tailWord_2907420, baseEnd_2907420] using wordTrace_append hprefix tailTrace_2907420
  have hstable : (prefixWord ++ tailWord_2907420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907420).length < 2 ^ (prefixWord ++ tailWord_2907420).sum := by decide
  have hdescent : baseEnd_2907420 < baseStart_2907420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907436 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_2907436 : Nat := 118140960795 + 2907436 * 2 ^ 59
def prefixEnd_2907436 : Nat := 4983230072969 + 3 ^ 40 * 2907436 * 2
def baseEnd_2907436 : Nat := 1492912140185591876978951

theorem tailTrace_2907436 : CollatzResearch.WordTrace tailWord_2907436 prefixEnd_2907436 1492912140185591876978951 := by
  unfold tailWord_2907436
  simp only [CollatzResearch.WordTrace]
  refine ⟨53021451347431698690751081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70695268463242264921001441 53021451347431698690751081)
  ·
    refine ⟨39766088510573774018063311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53021451347431698690751081 39766088510573774018063311)
    ·
      refine ⟨59649132765860661027094967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39766088510573774018063311 59649132765860661027094967)
      ·
        refine ⟨89473699148790991540642451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59649132765860661027094967 89473699148790991540642451)
        ·
          refine ⟨134210548723186487310963677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89473699148790991540642451 134210548723186487310963677)
          ·
            refine ⟨50328955771194932741611379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134210548723186487310963677 50328955771194932741611379)
            ·
              refine ⟨75493433656792399112417069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50328955771194932741611379 75493433656792399112417069)
              ·
                refine ⟨28310037621297149667156401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75493433656792399112417069 28310037621297149667156401)
                ·
                  refine ⟨21232528215972862250367301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28310037621297149667156401 21232528215972862250367301)
                  ·
                    refine ⟨3981099040494911671943869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21232528215972862250367301 3981099040494911671943869)
                    ·
                      refine ⟨1492912140185591876978951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981099040494911671943869 1492912140185591876978951)
                      ·
                        rfl

theorem cell23_2907436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_2907436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907436 prefixEnd_2907436 := by exact prefixLift 2907436
  have htrace : WordTrace (prefixWord ++ tailWord_2907436) baseStart_2907436 baseEnd_2907436 := by
    simpa [prefixWord, tailWord_2907436, baseEnd_2907436] using wordTrace_append hprefix tailTrace_2907436
  have hstable : (prefixWord ++ tailWord_2907436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907436).length < 2 ^ (prefixWord ++ tailWord_2907436).sum := by decide
  have hdescent : baseEnd_2907436 < baseStart_2907436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907473 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 5]
def baseStart_2907473 : Nat := 118140960795 + 2907473 * 2 ^ 59
def prefixEnd_2907473 : Nat := 4983230072969 + 3 ^ 40 * 2907473 * 2
def baseEnd_2907473 : Nat := 165881237663312025801809

theorem tailTrace_2907473 : CollatzResearch.WordTrace tailWord_2907473 prefixEnd_2907473 165881237663312025801809 := by
  unfold tailWord_2907473
  simp only [CollatzResearch.WordTrace]
  refine ⟨106044252195729352700599073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70696168130486235133732715 106044252195729352700599073)
  ·
    refine ⟨79533189146797014525449305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106044252195729352700599073 79533189146797014525449305)
    ·
      refine ⟨59649891860097760894086979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79533189146797014525449305 59649891860097760894086979)
      ·
        refine ⟨89474837790146641341130469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59649891860097760894086979 89474837790146641341130469)
        ·
          refine ⟨16776532085652495251461963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89474837790146641341130469 16776532085652495251461963)
          ·
            refine ⟨25164798128478742877192945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16776532085652495251461963 25164798128478742877192945)
            ·
              refine ⟨18873598596359057157894709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25164798128478742877192945 18873598596359057157894709)
              ·
                refine ⟨1769399868408661608552629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18873598596359057157894709 1769399868408661608552629)
                ·
                  refine ⟨165881237663312025801809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769399868408661608552629 165881237663312025801809)
                  ·
                    rfl

theorem cell23_2907473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 5].length) (baseStart_2907473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907473 prefixEnd_2907473 := by exact prefixLift 2907473
  have htrace : WordTrace (prefixWord ++ tailWord_2907473) baseStart_2907473 baseEnd_2907473 := by
    simpa [prefixWord, tailWord_2907473, baseEnd_2907473] using wordTrace_append hprefix tailTrace_2907473
  have hstable : (prefixWord ++ tailWord_2907473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907473).length < 2 ^ (prefixWord ++ tailWord_2907473).sum := by decide
  have hdescent : baseEnd_2907473 < baseStart_2907473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907478 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2907478 : Nat := 118140960795 + 2907478 * 2 ^ 59
def prefixEnd_2907478 : Nat := 4983230072969 + 3 ^ 40 * 2907478 * 2
def baseEnd_2907478 : Nat := 1492933706373080712653759

theorem tailTrace_2907478 : CollatzResearch.WordTrace tailWord_2907478 prefixEnd_2907478 1492933706373080712653759 := by
  unfold tailWord_2907478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627777160044452409658193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70696289707140825703020725 6627777160044452409658193)
  ·
    refine ⟨4970832870033339307243645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6627777160044452409658193 4970832870033339307243645)
    ·
      refine ⟨1864062326262502240216367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4970832870033339307243645 1864062326262502240216367)
      ·
        refine ⟨2796093489393753360324551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864062326262502240216367 2796093489393753360324551)
        ·
          refine ⟨4194140234090630040486827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796093489393753360324551 4194140234090630040486827)
          ·
            refine ⟨6291210351135945060730241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194140234090630040486827 6291210351135945060730241)
            ·
              refine ⟨4718407763351958795547681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6291210351135945060730241 4718407763351958795547681)
              ·
                refine ⟨3538805822513969096660761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718407763351958795547681 3538805822513969096660761)
                ·
                  refine ⟨2654104366885476822495571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538805822513969096660761 2654104366885476822495571)
                  ·
                    refine ⟨3981156550328215233743357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2654104366885476822495571 3981156550328215233743357)
                    ·
                      refine ⟨1492933706373080712653759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981156550328215233743357 1492933706373080712653759)
                      ·
                        rfl

theorem cell23_2907478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2907478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907478 prefixEnd_2907478 := by exact prefixLift 2907478
  have htrace : WordTrace (prefixWord ++ tailWord_2907478) baseStart_2907478 baseEnd_2907478 := by
    simpa [prefixWord, tailWord_2907478, baseEnd_2907478] using wordTrace_append hprefix tailTrace_2907478
  have hstable : (prefixWord ++ tailWord_2907478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907478).length < 2 ^ (prefixWord ++ tailWord_2907478).sum := by decide
  have hdescent : baseEnd_2907478 < baseStart_2907478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907490 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_2907490 : Nat := 118140960795 + 2907490 * 2 ^ 59
def prefixEnd_2907490 : Nat := 4983230072969 + 3 ^ 40 * 2907490 * 2
def baseEnd_2907490 : Nat := 165882207571214962855967

theorem tailTrace_2907490 : CollatzResearch.WordTrace tailWord_2907490 prefixEnd_2907490 165882207571214962855967 := by
  unfold tailWord_2907490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26511218059166941150991981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70696581491111843069311949 26511218059166941150991981)
  ·
    refine ⟨9941706772187602931621993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26511218059166941150991981 9941706772187602931621993)
    ·
      refine ⟨7456280079140702198716495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9941706772187602931621993 7456280079140702198716495)
      ·
        refine ⟨11184420118711053298074743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7456280079140702198716495 11184420118711053298074743)
        ·
          refine ⟨16776630178066579947112115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11184420118711053298074743 16776630178066579947112115)
          ·
            refine ⟨25164945267099869920668173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16776630178066579947112115 25164945267099869920668173)
            ·
              refine ⟨9436854475162451220250565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25164945267099869920668173 9436854475162451220250565)
              ·
                refine ⟨1769410214092959603796981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9436854475162451220250565 1769410214092959603796981)
                ·
                  refine ⟨165882207571214962855967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769410214092959603796981 165882207571214962855967)
                  ·
                    rfl

theorem cell23_2907490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2907490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907490 prefixEnd_2907490 := by exact prefixLift 2907490
  have htrace : WordTrace (prefixWord ++ tailWord_2907490) baseStart_2907490 baseEnd_2907490 := by
    simpa [prefixWord, tailWord_2907490, baseEnd_2907490] using wordTrace_append hprefix tailTrace_2907490
  have hstable : (prefixWord ++ tailWord_2907490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907490).length < 2 ^ (prefixWord ++ tailWord_2907490).sum := by decide
  have hdescent : baseEnd_2907490 < baseStart_2907490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907493 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_2907493 : Nat := 118140960795 + 2907493 * 2 ^ 59
def prefixEnd_2907493 : Nat := 4983230072969 + 3 ^ 40 * 2907493 * 2
def baseEnd_2907493 : Nat := 1492941408582898153966189

theorem tailTrace_2907493 : CollatzResearch.WordTrace tailWord_2907493 prefixEnd_2907493 1492941408582898153966189 := by
  unfold tailWord_2907493
  simp only [CollatzResearch.WordTrace]
  refine ⟨106044981655656896116327133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70696654437104597410884755 106044981655656896116327133)
  ·
    refine ⟨39766868120871336043622675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106044981655656896116327133 39766868120871336043622675)
    ·
      refine ⟨59650302181307004065434013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39766868120871336043622675 59650302181307004065434013)
      ·
        refine ⟨22368863317990126524537755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59650302181307004065434013 22368863317990126524537755)
        ·
          refine ⟨33553294976985189786806633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22368863317990126524537755 33553294976985189786806633)
          ·
            refine ⟨25164971232738892340104975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33553294976985189786806633 25164971232738892340104975)
            ·
              refine ⟨37747456849108338510157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25164971232738892340104975 37747456849108338510157463)
              ·
                refine ⟨56621185273662507765236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37747456849108338510157463 56621185273662507765236195)
                ·
                  refine ⟨84931777910493761647854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56621185273662507765236195 84931777910493761647854293)
                  ·
                    refine ⟨1990588544777197538621585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84931777910493761647854293 1990588544777197538621585)
                    ·
                      refine ⟨1492941408582898153966189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990588544777197538621585 1492941408582898153966189)
                      ·
                        rfl

theorem cell23_2907493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_2907493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907493 prefixEnd_2907493 := by exact prefixLift 2907493
  have htrace : WordTrace (prefixWord ++ tailWord_2907493) baseStart_2907493 baseEnd_2907493 := by
    simpa [prefixWord, tailWord_2907493, baseEnd_2907493] using wordTrace_append hprefix tailTrace_2907493
  have hstable : (prefixWord ++ tailWord_2907493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907493).length < 2 ^ (prefixWord ++ tailWord_2907493).sum := by decide
  have hdescent : baseEnd_2907493 < baseStart_2907493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907523 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_2907523 : Nat := 118140960795 + 2907523 * 2 ^ 59
def prefixEnd_2907523 : Nat := 4983230072969 + 3 ^ 40 * 2907523 * 2
def baseEnd_2907523 : Nat := 1492956813002533036591051

theorem tailTrace_2907523 : CollatzResearch.WordTrace tailWord_2907523 prefixEnd_2907523 1492956813002533036591051 := by
  unfold tailWord_2907523
  simp only [CollatzResearch.WordTrace]
  refine ⟨106046075845548211239919223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70697383897032140826612815 106046075845548211239919223)
  ·
    refine ⟨159069113768322316859878835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106046075845548211239919223 159069113768322316859878835)
    ·
      refine ⟨238603670652483475289818253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159069113768322316859878835 238603670652483475289818253)
      ·
        refine ⟨89476376494681303233681845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238603670652483475289818253 89476376494681303233681845)
        ·
          refine ⟨8388410296376372178157673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89476376494681303233681845 8388410296376372178157673)
          ·
            refine ⟨6291307722282279133618255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388410296376372178157673 6291307722282279133618255)
            ·
              refine ⟨9436961583423418700427383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291307722282279133618255 9436961583423418700427383)
              ·
                refine ⟨14155442375135128050641075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436961583423418700427383 14155442375135128050641075)
                ·
                  refine ⟨21233163562702692075961613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14155442375135128050641075 21233163562702692075961613)
                  ·
                    refine ⟨7962436336013509528485605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21233163562702692075961613 7962436336013509528485605)
                    ·
                      refine ⟨1492956813002533036591051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7962436336013509528485605 1492956813002533036591051)
                      ·
                        rfl

theorem cell23_2907523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_2907523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907523 prefixEnd_2907523 := by exact prefixLift 2907523
  have htrace : WordTrace (prefixWord ++ tailWord_2907523) baseStart_2907523 baseEnd_2907523 := by
    simpa [prefixWord, tailWord_2907523, baseEnd_2907523] using wordTrace_append hprefix tailTrace_2907523
  have hstable : (prefixWord ++ tailWord_2907523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907523).length < 2 ^ (prefixWord ++ tailWord_2907523).sum := by decide
  have hdescent : baseEnd_2907523 < baseStart_2907523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907543 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2907543 : Nat := 118140960795 + 2907543 * 2 ^ 59
def prefixEnd_2907543 : Nat := 4983230072969 + 3 ^ 40 * 2907543 * 2
def baseEnd_2907543 : Nat := 1492967082615622958340959

theorem tailTrace_2907543 : CollatzResearch.WordTrace tailWord_2907543 prefixEnd_2907543 1492967082615622958340959 := by
  unfold tailWord_2907543
  simp only [CollatzResearch.WordTrace]
  refine ⟨106046805305475754655647283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70697870203650503103764855 106046805305475754655647283)
  ·
    refine ⟨159070207958213631983470925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106046805305475754655647283 159070207958213631983470925)
    ·
      refine ⟨59651327984330111993801597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159070207958213631983470925 59651327984330111993801597)
      ·
        refine ⟨22369247994123791997675599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59651327984330111993801597 22369247994123791997675599)
        ·
          refine ⟨33553871991185687996513399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22369247994123791997675599 33553871991185687996513399)
          ·
            refine ⟨50330807986778531994770099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33553871991185687996513399 50330807986778531994770099)
            ·
              refine ⟨75496211980167797992155149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50330807986778531994770099 75496211980167797992155149)
              ·
                refine ⟨28311079492562924247058181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75496211980167797992155149 28311079492562924247058181)
                ·
                  refine ⟨5308327404855548296323409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28311079492562924247058181 5308327404855548296323409)
                  ·
                    refine ⟨3981245553641661222242557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5308327404855548296323409 3981245553641661222242557)
                    ·
                      refine ⟨1492967082615622958340959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981245553641661222242557 1492967082615622958340959)
                      ·
                        rfl

theorem cell23_2907543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2907543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907543 prefixEnd_2907543 := by exact prefixLift 2907543
  have htrace : WordTrace (prefixWord ++ tailWord_2907543) baseStart_2907543 baseEnd_2907543 := by
    simpa [prefixWord, tailWord_2907543, baseEnd_2907543] using wordTrace_append hprefix tailTrace_2907543
  have hstable : (prefixWord ++ tailWord_2907543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907543).length < 2 ^ (prefixWord ++ tailWord_2907543).sum := by decide
  have hdescent : baseEnd_2907543 < baseStart_2907543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907600 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2]
def baseStart_2907600 : Nat := 118140960795 + 2907600 * 2 ^ 59
def prefixEnd_2907600 : Nat := 4983230072969 + 3 ^ 40 * 2907600 * 2
def baseEnd_2907600 : Nat := 1492996351012929235328197

theorem tailTrace_2907600 : CollatzResearch.WordTrace tailWord_2907600 prefixEnd_2907600 1492996351012929235328197 := by
  unfold tailWord_2907600
  simp only [CollatzResearch.WordTrace]
  refine ⟨53024442133134626695236127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70699256177512835593648169 53024442133134626695236127)
  ·
    refine ⟨79536663199701940042854191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53024442133134626695236127 79536663199701940042854191)
    ·
      refine ⟨119304994799552910064281287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79536663199701940042854191 119304994799552910064281287)
      ·
        refine ⟨178957492199329365096421931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119304994799552910064281287 178957492199329365096421931)
        ·
          refine ⟨268436238298994047644632897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178957492199329365096421931 268436238298994047644632897)
          ·
            refine ⟨201327178724245535733474673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268436238298994047644632897 201327178724245535733474673)
            ·
              refine ⟨150995384043184151800106005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201327178724245535733474673 150995384043184151800106005)
              ·
                refine ⟨7077908627024257115629969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150995384043184151800106005 7077908627024257115629969)
                ·
                  refine ⟨5308431470268192836722477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077908627024257115629969 5308431470268192836722477)
                  ·
                    refine ⟨1990661801350572313770929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5308431470268192836722477 1990661801350572313770929)
                    ·
                      refine ⟨1492996351012929235328197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990661801350572313770929 1492996351012929235328197)
                      ·
                        rfl

theorem cell23_2907600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2].length) (baseStart_2907600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907600 prefixEnd_2907600 := by exact prefixLift 2907600
  have htrace : WordTrace (prefixWord ++ tailWord_2907600) baseStart_2907600 baseEnd_2907600 := by
    simpa [prefixWord, tailWord_2907600, baseEnd_2907600] using wordTrace_append hprefix tailTrace_2907600
  have hstable : (prefixWord ++ tailWord_2907600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907600).length < 2 ^ (prefixWord ++ tailWord_2907600).sum := by decide
  have hdescent : baseEnd_2907600 < baseStart_2907600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_2907607 : Nat := 118140960795 + 2907607 * 2 ^ 59
def prefixEnd_2907607 : Nat := 4983230072969 + 3 ^ 40 * 2907607 * 2
def baseEnd_2907607 : Nat := 1492999945377510707940665

theorem tailTrace_2907607 : CollatzResearch.WordTrace tailWord_2907607 prefixEnd_2907607 1492999945377510707940665 := by
  unfold tailWord_2907607
  simp only [CollatzResearch.WordTrace]
  refine ⟨106049139577243893585977075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70699426384829262390651383 106049139577243893585977075)
  ·
    refine ⟨159073709365865840378965613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106049139577243893585977075 159073709365865840378965613)
    ·
      refine ⟨59652641012199690142112105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159073709365865840378965613 59652641012199690142112105)
      ·
        refine ⟨44739480759149767606584079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59652641012199690142112105 44739480759149767606584079)
        ·
          refine ⟨67109221138724651409876119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44739480759149767606584079 67109221138724651409876119)
          ·
            refine ⟨100663831708086977114814179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67109221138724651409876119 100663831708086977114814179)
            ·
              refine ⟨150995747562130465672221269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100663831708086977114814179 150995747562130465672221269)
              ·
                refine ⟨1769481416743716394596343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 150995747562130465672221269 1769481416743716394596343)
                ·
                  refine ⟨2654222125115574591894515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769481416743716394596343 2654222125115574591894515)
                  ·
                    refine ⟨3981333187673361887841773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2654222125115574591894515 3981333187673361887841773)
                    ·
                      refine ⟨1492999945377510707940665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981333187673361887841773 1492999945377510707940665)
                      ·
                        rfl

theorem cell23_2907607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_2907607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907607 prefixEnd_2907607 := by exact prefixLift 2907607
  have htrace : WordTrace (prefixWord ++ tailWord_2907607) baseStart_2907607 baseEnd_2907607 := by
    simpa [prefixWord, tailWord_2907607, baseEnd_2907607] using wordTrace_append hprefix tailTrace_2907607
  have hstable : (prefixWord ++ tailWord_2907607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907607).length < 2 ^ (prefixWord ++ tailWord_2907607).sum := by decide
  have hdescent : baseEnd_2907607 < baseStart_2907607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907630 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2907630 : Nat := 118140960795 + 2907630 * 2 ^ 59
def prefixEnd_2907630 : Nat := 4983230072969 + 3 ^ 40 * 2907630 * 2
def baseEnd_2907630 : Nat := 1493011755432564117953059

theorem tailTrace_2907630 : CollatzResearch.WordTrace tailWord_2907630 prefixEnd_2907630 1493011755432564117953059 := by
  unfold tailWord_2907630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13256247307020071064258043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70699985637440379009376229 13256247307020071064258043)
  ·
    refine ⟨19884370960530106596387065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13256247307020071064258043 19884370960530106596387065)
    ·
      refine ⟨14913278220397579947290299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19884370960530106596387065 14913278220397579947290299)
      ·
        refine ⟨22369917330596369920935449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913278220397579947290299 22369917330596369920935449)
        ·
          refine ⟨16777437997947277440701587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22369917330596369920935449 16777437997947277440701587)
          ·
            refine ⟨25166156996920916161052381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16777437997947277440701587 25166156996920916161052381)
            ·
              refine ⟨9437308873845343560394643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25166156996920916161052381 9437308873845343560394643)
              ·
                refine ⟨14155963310768015340591965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9437308873845343560394643 14155963310768015340591965)
                ·
                  refine ⟨5308486241538005752721987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14155963310768015340591965 5308486241538005752721987)
                  ·
                    refine ⟨7962729362307008629082981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308486241538005752721987 7962729362307008629082981)
                    ·
                      refine ⟨1493011755432564117953059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7962729362307008629082981 1493011755432564117953059)
                      ·
                        rfl

theorem cell23_2907630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2907630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907630 prefixEnd_2907630 := by exact prefixLift 2907630
  have htrace : WordTrace (prefixWord ++ tailWord_2907630) baseStart_2907630 baseEnd_2907630 := by
    simpa [prefixWord, tailWord_2907630, baseEnd_2907630] using wordTrace_append hprefix tailTrace_2907630
  have hstable : (prefixWord ++ tailWord_2907630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907630).length < 2 ^ (prefixWord ++ tailWord_2907630).sum := by decide
  have hdescent : baseEnd_2907630 < baseStart_2907630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907634 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2907634 : Nat := 118140960795 + 2907634 * 2 ^ 59
def prefixEnd_2907634 : Nat := 4983230072969 + 3 ^ 40 * 2907634 * 2
def baseEnd_2907634 : Nat := 1493013809355182102303041

theorem tailTrace_2907634 : CollatzResearch.WordTrace tailWord_2907634 prefixEnd_2907634 1493013809355182102303041 := by
  unfold tailWord_2907634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26512531087036519299302489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70700082898764051464806637 26512531087036519299302489)
  ·
    refine ⟨19884398315277389474476867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26512531087036519299302489 19884398315277389474476867)
    ·
      refine ⟨29826597472916084211715301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19884398315277389474476867 29826597472916084211715301)
      ·
        refine ⟨5592487026171765789696619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29826597472916084211715301 5592487026171765789696619)
        ·
          refine ⟨8388730539257648684544929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592487026171765789696619 8388730539257648684544929)
          ·
            refine ⟨6291547904443236513408697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388730539257648684544929 6291547904443236513408697)
            ·
              refine ⟨4718660928332427385056523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6291547904443236513408697 4718660928332427385056523)
              ·
                refine ⟨7077991392498641077584785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718660928332427385056523 7077991392498641077584785)
                ·
                  refine ⟨5308493544373980808188589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077991392498641077584785 5308493544373980808188589)
                  ·
                    refine ⟨1990685079140242803070721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5308493544373980808188589 1990685079140242803070721)
                    ·
                      refine ⟨1493013809355182102303041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990685079140242803070721 1493013809355182102303041)
                      ·
                        rfl

theorem cell23_2907634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2907634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907634 prefixEnd_2907634 := by exact prefixLift 2907634
  have htrace : WordTrace (prefixWord ++ tailWord_2907634) baseStart_2907634 baseEnd_2907634 := by
    simpa [prefixWord, tailWord_2907634, baseEnd_2907634] using wordTrace_append hprefix tailTrace_2907634
  have hstable : (prefixWord ++ tailWord_2907634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907634).length < 2 ^ (prefixWord ++ tailWord_2907634).sum := by decide
  have hdescent : baseEnd_2907634 < baseStart_2907634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907643 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_2907643 : Nat := 118140960795 + 2907643 * 2 ^ 59
def prefixEnd_2907643 : Nat := 4983230072969 + 3 ^ 40 * 2907643 * 2
def baseEnd_2907643 : Nat := 1493018430681072567090499

theorem tailTrace_2907643 : CollatzResearch.WordTrace tailWord_2907643 prefixEnd_2907643 1493018430681072567090499 := by
  unfold tailWord_2907643
  simp only [CollatzResearch.WordTrace]
  refine ⟨106050452605113471734287583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70700301736742314489525055 106050452605113471734287583)
  ·
    refine ⟨159075678907670207601431375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106050452605113471734287583 159075678907670207601431375)
    ·
      refine ⟨238613518361505311402147063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159075678907670207601431375 238613518361505311402147063)
      ·
        refine ⟨357920277542257967103220595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238613518361505311402147063 357920277542257967103220595)
        ·
          refine ⟨536880416313386950654830893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357920277542257967103220595 536880416313386950654830893)
          ·
            refine ⟨201330156117520106495561585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536880416313386950654830893 201330156117520106495561585)
            ·
              refine ⟨150997617088140079871671189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201330156117520106495561585 150997617088140079871671189)
              ·
                refine ⟨7078013301006566243984587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150997617088140079871671189 7078013301006566243984587)
                ·
                  refine ⟨10617019951509849365976881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078013301006566243984587 10617019951509849365976881)
                  ·
                    refine ⟨7962764963632387024482661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10617019951509849365976881 7962764963632387024482661)
                    ·
                      refine ⟨1493018430681072567090499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7962764963632387024482661 1493018430681072567090499)
                      ·
                        rfl

theorem cell23_2907643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_2907643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907643 prefixEnd_2907643 := by exact prefixLift 2907643
  have htrace : WordTrace (prefixWord ++ tailWord_2907643) baseStart_2907643 baseEnd_2907643 := by
    simpa [prefixWord, tailWord_2907643, baseEnd_2907643] using wordTrace_append hprefix tailTrace_2907643
  have hstable : (prefixWord ++ tailWord_2907643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907643).length < 2 ^ (prefixWord ++ tailWord_2907643).sum := by decide
  have hdescent : baseEnd_2907643 < baseStart_2907643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907720 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_2907720 : Nat := 118140960795 + 2907720 * 2 ^ 59
def prefixEnd_2907720 : Nat := 4983230072969 + 3 ^ 40 * 2907720 * 2
def baseEnd_2907720 : Nat := 1493057968691468765827645

theorem tailTrace_2907720 : CollatzResearch.WordTrace tailWord_2907720 prefixEnd_2907720 1493057968691468765827645 := by
  unfold tailWord_2907720
  simp only [CollatzResearch.WordTrace]
  refine ⟨53026630512917256942420307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70702174017223009256560409 53026630512917256942420307)
  ·
    refine ⟨79539945769375885413630461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53026630512917256942420307 79539945769375885413630461)
    ·
      refine ⟨29827479663515957030111423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79539945769375885413630461 29827479663515957030111423)
      ·
        refine ⟨44741219495273935545167135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29827479663515957030111423 44741219495273935545167135)
        ·
          refine ⟨67111829242910903317750703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44741219495273935545167135 67111829242910903317750703)
          ·
            refine ⟨100667743864366354976626055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67111829242910903317750703 100667743864366354976626055)
            ·
              refine ⟨151001615796549532464939083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100667743864366354976626055 151001615796549532464939083)
              ·
                refine ⟨226502423694824298697408625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151001615796549532464939083 226502423694824298697408625)
                ·
                  refine ⟨169876817771118224023056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226502423694824298697408625 169876817771118224023056469)
                  ·
                    refine ⟨1990743958255291687770193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 169876817771118224023056469 1990743958255291687770193)
                    ·
                      refine ⟨1493057968691468765827645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990743958255291687770193 1493057968691468765827645)
                      ·
                        rfl

theorem cell23_2907720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_2907720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907720 prefixEnd_2907720 := by exact prefixLift 2907720
  have htrace : WordTrace (prefixWord ++ tailWord_2907720) baseStart_2907720 baseEnd_2907720 := by
    simpa [prefixWord, tailWord_2907720, baseEnd_2907720] using wordTrace_append hprefix tailTrace_2907720
  have hstable : (prefixWord ++ tailWord_2907720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907720).length < 2 ^ (prefixWord ++ tailWord_2907720).sum := by decide
  have hdescent : baseEnd_2907720 < baseStart_2907720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_2907723 : Nat := 118140960795 + 2907723 * 2 ^ 59
def prefixEnd_2907723 : Nat := 4983230072969 + 3 ^ 40 * 2907723 * 2
def baseEnd_2907723 : Nat := 1493059509133432254090131

theorem tailTrace_2907723 : CollatzResearch.WordTrace tailWord_2907723 prefixEnd_2907723 1493059509133432254090131 := by
  unfold tailWord_2907723
  simp only [CollatzResearch.WordTrace]
  refine ⟨106053370444823645397199823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70702246963215763598133215 106053370444823645397199823)
  ·
    refine ⟨159080055667235468095799735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106053370444823645397199823 159080055667235468095799735)
    ·
      refine ⟨238620083500853202143699603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159080055667235468095799735 238620083500853202143699603)
      ·
        refine ⟨357930125251279803215549405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238620083500853202143699603 357930125251279803215549405)
        ·
          refine ⟨134223796969229926205831027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357930125251279803215549405 134223796969229926205831027)
          ·
            refine ⟨201335695453844889308746541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134223796969229926205831027 201335695453844889308746541)
            ·
              refine ⟨75500885795191833490779953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201335695453844889308746541 75500885795191833490779953)
              ·
                refine ⟨56625664346393875118084965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75500885795191833490779953 56625664346393875118084965)
                ·
                  refine ⟨10617312064948851584640931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56625664346393875118084965 10617312064948851584640931)
                  ·
                    refine ⟨15925968097423277376961397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10617312064948851584640931 15925968097423277376961397)
                    ·
                      refine ⟨1493059509133432254090131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15925968097423277376961397 1493059509133432254090131)
                      ·
                        rfl

theorem cell23_2907723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_2907723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907723 prefixEnd_2907723 := by exact prefixLift 2907723
  have htrace : WordTrace (prefixWord ++ tailWord_2907723) baseStart_2907723 baseEnd_2907723 := by
    simpa [prefixWord, tailWord_2907723, baseEnd_2907723] using wordTrace_append hprefix tailTrace_2907723
  have hstable : (prefixWord ++ tailWord_2907723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907723).length < 2 ^ (prefixWord ++ tailWord_2907723).sum := by decide
  have hdescent : baseEnd_2907723 < baseStart_2907723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907730 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2907730 : Nat := 118140960795 + 2907730 * 2 ^ 59
def prefixEnd_2907730 : Nat := 4983230072969 + 3 ^ 40 * 2907730 * 2
def baseEnd_2907730 : Nat := 497687701166004575567533

theorem tailTrace_2907730 : CollatzResearch.WordTrace tailWord_2907730 prefixEnd_2907730 497687701166004575567533 := by
  unfold tailWord_2907730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513406438949571398176161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70702417170532190395136429 26513406438949571398176161)
  ·
    refine ⟨19885054829212178548632121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26513406438949571398176161 19885054829212178548632121)
    ·
      refine ⟨14913791121909133911474091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19885054829212178548632121 14913791121909133911474091)
      ·
        refine ⟨22370686682863700867211137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913791121909133911474091 22370686682863700867211137)
        ·
          refine ⟨16778015012147775650408353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22370686682863700867211137 16778015012147775650408353)
          ·
            refine ⟨12583511259110831737806265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16778015012147775650408353 12583511259110831737806265)
            ·
              refine ⟨9437633444333123803354699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12583511259110831737806265 9437633444333123803354699)
              ·
                refine ⟨14156450166499685705032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9437633444333123803354699 14156450166499685705032049)
                ·
                  refine ⟨10617337624874764278774037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14156450166499685705032049 10617337624874764278774037)
                  ·
                    refine ⟨497687701166004575567533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10617337624874764278774037 497687701166004575567533)
                    ·
                      rfl

theorem cell23_2907730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2907730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907730 prefixEnd_2907730 := by exact prefixLift 2907730
  have htrace : WordTrace (prefixWord ++ tailWord_2907730) baseStart_2907730 baseEnd_2907730 := by
    simpa [prefixWord, tailWord_2907730, baseEnd_2907730] using wordTrace_append hprefix tailTrace_2907730
  have hstable : (prefixWord ++ tailWord_2907730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907730).length < 2 ^ (prefixWord ++ tailWord_2907730).sum := by decide
  have hdescent : baseEnd_2907730 < baseStart_2907730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907754 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2907754 : Nat := 118140960795 + 2907754 * 2 ^ 59
def prefixEnd_2907754 : Nat := 4983230072969 + 3 ^ 40 * 2907754 * 2
def baseEnd_2907754 : Nat := 1493075427033721632802489

theorem tailTrace_2907754 : CollatzResearch.WordTrace tailWord_2907754 prefixEnd_2907754 1493075427033721632802489 := by
  unfold tailWord_2907754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513625276927834422894579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70703000738474225127718877 26513625276927834422894579)
  ·
    refine ⟨39770437915391751634341869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26513625276927834422894579 39770437915391751634341869)
    ·
      refine ⟨14913914218271906862878201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39770437915391751634341869 14913914218271906862878201)
      ·
        refine ⟨11185435663703930147158651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14913914218271906862878201 11185435663703930147158651)
        ·
          refine ⟨16778153495555895220737977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185435663703930147158651 16778153495555895220737977)
          ·
            refine ⟨12583615121666921415553483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16778153495555895220737977 12583615121666921415553483)
            ·
              refine ⟨18875422682500382123330225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12583615121666921415553483 18875422682500382123330225)
              ·
                refine ⟨14156567011875286592497669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18875422682500382123330225 14156567011875286592497669)
                ·
                  refine ⟨2654356314726616236093313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14156567011875286592497669 2654356314726616236093313)
                  ·
                    refine ⟨1990767236044962177069985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654356314726616236093313 1990767236044962177069985)
                    ·
                      refine ⟨1493075427033721632802489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990767236044962177069985 1493075427033721632802489)
                      ·
                        rfl

theorem cell23_2907754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2907754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907754 prefixEnd_2907754 := by exact prefixLift 2907754
  have htrace : WordTrace (prefixWord ++ tailWord_2907754) baseStart_2907754 baseEnd_2907754 := by
    simpa [prefixWord, tailWord_2907754, baseEnd_2907754] using wordTrace_append hprefix tailTrace_2907754
  have hstable : (prefixWord ++ tailWord_2907754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907754).length < 2 ^ (prefixWord ++ tailWord_2907754).sum := by decide
  have hdescent : baseEnd_2907754 < baseStart_2907754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907757 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2907757 : Nat := 118140960795 + 2907757 * 2 ^ 59
def prefixEnd_2907757 : Nat := 4983230072969 + 3 ^ 40 * 2907757 * 2
def baseEnd_2907757 : Nat := 1493076967475685121064975

theorem tailTrace_2907757 : CollatzResearch.WordTrace tailWord_2907757 prefixEnd_2907757 1493076967475685121064975 := by
  unfold tailWord_2907757
  simp only [CollatzResearch.WordTrace]
  refine ⟨106054610526700469203937525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70703073684466979469291683 106054610526700469203937525)
  ·
    refine ⟨9942619736878168987869143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106054610526700469203937525 9942619736878168987869143)
    ·
      refine ⟨14913929605317253481803715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9942619736878168987869143 14913929605317253481803715)
      ·
        refine ⟨22370894407975880222705573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14913929605317253481803715 22370894407975880222705573)
        ·
          refine ⟨4194542701495477541757295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22370894407975880222705573 4194542701495477541757295)
          ·
            refine ⟨6291814052243216312635943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194542701495477541757295 6291814052243216312635943)
            ·
              refine ⟨9437721078364824468953915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6291814052243216312635943 9437721078364824468953915)
              ·
                refine ⟨14156581617547236703430873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9437721078364824468953915 14156581617547236703430873)
                ·
                  refine ⟨10617436213160427527573155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14156581617547236703430873 10617436213160427527573155)
                  ·
                    refine ⟨15926154319740641291359733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10617436213160427527573155 15926154319740641291359733)
                    ·
                      refine ⟨1493076967475685121064975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15926154319740641291359733 1493076967475685121064975)
                      ·
                        rfl

theorem cell23_2907757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2907757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907757 prefixEnd_2907757 := by exact prefixLift 2907757
  have htrace : WordTrace (prefixWord ++ tailWord_2907757) baseStart_2907757 baseEnd_2907757 := by
    simpa [prefixWord, tailWord_2907757, baseEnd_2907757] using wordTrace_append hprefix tailTrace_2907757
  have hstable : (prefixWord ++ tailWord_2907757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907757).length < 2 ^ (prefixWord ++ tailWord_2907757).sum := by decide
  have hdescent : baseEnd_2907757 < baseStart_2907757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907770 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_2907770 : Nat := 118140960795 + 2907770 * 2 ^ 59
def prefixEnd_2907770 : Nat := 4983230072969 + 3 ^ 40 * 2907770 * 2
def baseEnd_2907770 : Nat := 1493083642724193570202415

theorem tailTrace_2907770 : CollatzResearch.WordTrace tailWord_2907770 prefixEnd_2907770 1493083642724193570202415 := by
  unfold tailWord_2907770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513771168913343106040191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70703389783768914949440509 26513771168913343106040191)
  ·
    refine ⟨39770656753370014659060287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26513771168913343106040191 39770656753370014659060287)
    ·
      refine ⟨59655985130055021988590431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39770656753370014659060287 59655985130055021988590431)
      ·
        refine ⟨89483977695082532982885647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59655985130055021988590431 89483977695082532982885647)
        ·
          refine ⟨134225966542623799474328471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89483977695082532982885647 134225966542623799474328471)
          ·
            refine ⟨201338949813935699211492707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134225966542623799474328471 201338949813935699211492707)
            ·
              refine ⟨302008424720903548817239061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201338949813935699211492707 302008424720903548817239061)
              ·
                refine ⟨14156644908792353850808081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302008424720903548817239061 14156644908792353850808081)
                ·
                  refine ⟨10617483681594265388106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14156644908792353850808081 10617483681594265388106061)
                  ·
                    refine ⟨3981556380597849520539773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10617483681594265388106061 3981556380597849520539773)
                    ·
                      refine ⟨1493083642724193570202415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981556380597849520539773 1493083642724193570202415)
                      ·
                        rfl

theorem cell23_2907770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_2907770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907770 prefixEnd_2907770 := by exact prefixLift 2907770
  have htrace : WordTrace (prefixWord ++ tailWord_2907770) baseStart_2907770 baseEnd_2907770 := by
    simpa [prefixWord, tailWord_2907770, baseEnd_2907770] using wordTrace_append hprefix tailTrace_2907770
  have hstable : (prefixWord ++ tailWord_2907770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907770).length < 2 ^ (prefixWord ++ tailWord_2907770).sum := by decide
  have hdescent : baseEnd_2907770 < baseStart_2907770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907777 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 7]
def baseStart_2907777 : Nat := 118140960795 + 2907777 * 2 ^ 59
def prefixEnd_2907777 : Nat := 4983230072969 + 3 ^ 40 * 2907777 * 2
def baseEnd_2907777 : Nat := 165898581898752782534987

theorem tailTrace_2907777 : CollatzResearch.WordTrace tailWord_2907777 prefixEnd_2907777 165898581898752782534987 := by
  unfold tailWord_2907777
  simp only [CollatzResearch.WordTrace]
  refine ⟨106055339986628012619665585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70703559991085341746443723 106055339986628012619665585)
  ·
    refine ⟨79541504989971009464749189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106055339986628012619665585 79541504989971009464749189)
    ·
      refine ⟨14914032185619564274640473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79541504989971009464749189 14914032185619564274640473)
      ·
        refine ⟨11185524139214673205980355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14914032185619564274640473 11185524139214673205980355)
        ·
          refine ⟨16778286208822009808970533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185524139214673205980355 16778286208822009808970533)
          ·
            refine ⟨3145928664154126839181975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16778286208822009808970533 3145928664154126839181975)
            ·
              refine ⟨4718892996231190258772963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145928664154126839181975 4718892996231190258772963)
              ·
                refine ⟨7078339494346785388159445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718892996231190258772963 7078339494346785388159445)
                ·
                  refine ⟨165898581898752782534987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7078339494346785388159445 165898581898752782534987)
                  ·
                    rfl

theorem cell23_2907777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_2907777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907777 prefixEnd_2907777 := by exact prefixLift 2907777
  have htrace : WordTrace (prefixWord ++ tailWord_2907777) baseStart_2907777 baseEnd_2907777 := by
    simpa [prefixWord, tailWord_2907777, baseEnd_2907777] using wordTrace_append hprefix tailTrace_2907777
  have hstable : (prefixWord ++ tailWord_2907777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907777).length < 2 ^ (prefixWord ++ tailWord_2907777).sum := by decide
  have hdescent : baseEnd_2907777 < baseStart_2907777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907827 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 4, 2]
def baseStart_2907827 : Nat := 118140960795 + 2907827 * 2 ^ 59
def prefixEnd_2907827 : Nat := 4983230072969 + 3 ^ 40 * 2907827 * 2
def baseEnd_2907827 : Nat := 1493112911121499847189653

theorem tailTrace_2907827 : CollatzResearch.WordTrace tailWord_2907827 prefixEnd_2907827 1493112911121499847189653 := by
  unfold tailWord_2907827
  simp only [CollatzResearch.WordTrace]
  refine ⟨106057163636446871158985735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70704775757631247439323823 106057163636446871158985735)
  ·
    refine ⟨159085745454670306738478603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106057163636446871158985735 159085745454670306738478603)
    ·
      refine ⟨238628618182005460107717905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159085745454670306738478603 238628618182005460107717905)
      ·
        refine ⟨178971463636504095080788429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238628618182005460107717905 178971463636504095080788429)
        ·
          refine ⟨67114298863689035655295661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178971463636504095080788429 67114298863689035655295661)
          ·
            refine ⟨25167862073883388370735873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67114298863689035655295661 25167862073883388370735873)
            ·
              refine ⟨18875896555412541278051905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25167862073883388370735873 18875896555412541278051905)
              ·
                refine ⟨14156922416559405958538929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18875896555412541278051905 14156922416559405958538929)
                ·
                  refine ⟨10617691812419554468904197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14156922416559405958538929 10617691812419554468904197)
                  ·
                    refine ⟨1990817214828666462919537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10617691812419554468904197 1990817214828666462919537)
                    ·
                      refine ⟨1493112911121499847189653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990817214828666462919537 1493112911121499847189653)
                      ·
                        rfl

theorem cell23_2907827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4, 2].length) (baseStart_2907827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907827 prefixEnd_2907827 := by exact prefixLift 2907827
  have htrace : WordTrace (prefixWord ++ tailWord_2907827) baseStart_2907827 baseEnd_2907827 := by
    simpa [prefixWord, tailWord_2907827, baseEnd_2907827] using wordTrace_append hprefix tailTrace_2907827
  have hstable : (prefixWord ++ tailWord_2907827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907827).length < 2 ^ (prefixWord ++ tailWord_2907827).sum := by decide
  have hdescent : baseEnd_2907827 < baseStart_2907827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907837 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2907837 : Nat := 118140960795 + 2907837 * 2 ^ 59
def prefixEnd_2907837 : Nat := 4983230072969 + 3 ^ 40 * 2907837 * 2
def baseEnd_2907837 : Nat := 497706015309348269354869

theorem tailTrace_2907837 : CollatzResearch.WordTrace tailWord_2907837 prefixEnd_2907837 497706015309348269354869 := by
  unfold tailWord_2907837
  simp only [CollatzResearch.WordTrace]
  refine ⟨106057528366410642866849765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70705018910940428577899843 106057528366410642866849765)
  ·
    refine ⟨19885786568701995537534331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106057528366410642866849765 19885786568701995537534331)
    ·
      refine ⟨29828679853052993306301497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19885786568701995537534331 29828679853052993306301497)
      ·
        refine ⟨22371509889789744979726123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29828679853052993306301497 22371509889789744979726123)
        ·
          refine ⟨33557264834684617469589185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22371509889789744979726123 33557264834684617469589185)
          ·
            refine ⟨25167948626013463102191889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33557264834684617469589185 25167948626013463102191889)
            ·
              refine ⟨18875961469510097326643917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25167948626013463102191889 18875961469510097326643917)
              ·
                refine ⟨7078485551066286497491469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18875961469510097326643917 7078485551066286497491469)
                ·
                  refine ⟨2654432081649857436559301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7078485551066286497491469 2654432081649857436559301)
                  ·
                    refine ⟨497706015309348269354869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654432081649857436559301 497706015309348269354869)
                    ·
                      rfl

theorem cell23_2907837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2907837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907837 prefixEnd_2907837 := by exact prefixLift 2907837
  have htrace : WordTrace (prefixWord ++ tailWord_2907837) baseStart_2907837 baseEnd_2907837 := by
    simpa [prefixWord, tailWord_2907837, baseEnd_2907837] using wordTrace_append hprefix tailTrace_2907837
  have hstable : (prefixWord ++ tailWord_2907837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907837).length < 2 ^ (prefixWord ++ tailWord_2907837).sum := by decide
  have hdescent : baseEnd_2907837 < baseStart_2907837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907844 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2907844 : Nat := 118140960795 + 2907844 * 2 ^ 59
def prefixEnd_2907844 : Nat := 4983230072969 + 3 ^ 40 * 2907844 * 2
def baseEnd_2907844 : Nat := 1493121640292626280677075

theorem tailTrace_2907844 : CollatzResearch.WordTrace tailWord_2907844 prefixEnd_2907844 1493121640292626280677075 := by
  unfold tailWord_2907844
  simp only [CollatzResearch.WordTrace]
  refine ⟨53028891838692641531177293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70705189118256855374903057 53028891838692641531177293)
  ·
    refine ⟨19885834439509740574191485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53028891838692641531177293 19885834439509740574191485)
    ·
      refine ⟨7457187914816152715321807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19885834439509740574191485 7457187914816152715321807)
      ·
        refine ⟨11185781872224229072982711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457187914816152715321807 11185781872224229072982711)
        ·
          refine ⟨16778672808336343609474067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11185781872224229072982711 16778672808336343609474067)
          ·
            refine ⟨25168009212504515414211101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16778672808336343609474067 25168009212504515414211101)
            ·
              refine ⟨9438003454689193280329163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25168009212504515414211101 9438003454689193280329163)
              ·
                refine ⟨14157005182033789920493745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438003454689193280329163 14157005182033789920493745)
                ·
                  refine ⟨10617753886525342440370309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14157005182033789920493745 10617753886525342440370309)
                  ·
                    refine ⟨1990828853723501707569433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10617753886525342440370309 1990828853723501707569433)
                    ·
                      refine ⟨1493121640292626280677075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990828853723501707569433 1493121640292626280677075)
                      ·
                        rfl

theorem cell23_2907844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2907844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907844 prefixEnd_2907844 := by exact prefixLift 2907844
  have htrace : WordTrace (prefixWord ++ tailWord_2907844) baseStart_2907844 baseEnd_2907844 := by
    simpa [prefixWord, tailWord_2907844, baseEnd_2907844] using wordTrace_append hprefix tailTrace_2907844
  have hstable : (prefixWord ++ tailWord_2907844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907844).length < 2 ^ (prefixWord ++ tailWord_2907844).sum := by decide
  have hdescent : baseEnd_2907844 < baseStart_2907844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907914 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_2907914 : Nat := 118140960795 + 2907914 * 2 ^ 59
def prefixEnd_2907914 : Nat := 4983230072969 + 3 ^ 40 * 2907914 * 2
def baseEnd_2907914 : Nat := 497719194646147002267251

theorem tailTrace_2907914 : CollatzResearch.WordTrace tailWord_2907914 prefixEnd_2907914 497719194646147002267251 := by
  unfold tailWord_2907914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515084196782921254350699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70706891191421123344935197 26515084196782921254350699)
  ·
    refine ⟨39772626295174381881526049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26515084196782921254350699 39772626295174381881526049)
    ·
      refine ⟨29829469721380786411144537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39772626295174381881526049 29829469721380786411144537)
      ·
        refine ⟨22372102291035589808358403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29829469721380786411144537 22372102291035589808358403)
        ·
          refine ⟨33558153436553384712537605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22372102291035589808358403 33558153436553384712537605)
          ·
            refine ⟨6292153769353759633600801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33558153436553384712537605 6292153769353759633600801)
            ·
              refine ⟨4719115327015319725200601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6292153769353759633600801 4719115327015319725200601)
              ·
                refine ⟨3539336495261489793900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719115327015319725200601 3539336495261489793900451)
                ·
                  refine ⟨5309004742892234690850677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539336495261489793900451 5309004742892234690850677)
                  ·
                    refine ⟨497719194646147002267251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5309004742892234690850677 497719194646147002267251)
                    ·
                      rfl

theorem cell23_2907914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_2907914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907914 prefixEnd_2907914 := by exact prefixLift 2907914
  have htrace : WordTrace (prefixWord ++ tailWord_2907914) baseStart_2907914 baseEnd_2907914 := by
    simpa [prefixWord, tailWord_2907914, baseEnd_2907914] using wordTrace_append hprefix tailTrace_2907914
  have hstable : (prefixWord ++ tailWord_2907914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907914).length < 2 ^ (prefixWord ++ tailWord_2907914).sum := by decide
  have hdescent : baseEnd_2907914 < baseStart_2907914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907937 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2907937 : Nat := 118140960795 + 2907937 * 2 ^ 59
def prefixEnd_2907937 : Nat := 4983230072969 + 3 ^ 40 * 2907937 * 2
def baseEnd_2907937 : Nat := 1493169393993494416814147

theorem tailTrace_2907937 : CollatzResearch.WordTrace tailWord_2907937 prefixEnd_2907937 1493169393993494416814147 := by
  unfold tailWord_2907937
  simp only [CollatzResearch.WordTrace]
  refine ⟨106061175666048359945490065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70707450444032239963660043 106061175666048359945490065)
  ·
    refine ⟨79545881749536269959117549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106061175666048359945490065 79545881749536269959117549)
    ·
      refine ⟨29829705656076101234669081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79545881749536269959117549 29829705656076101234669081)
      ·
        refine ⟨22372279242057075926001811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29829705656076101234669081 22372279242057075926001811)
        ·
          refine ⟨33558418863085613889002717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22372279242057075926001811 33558418863085613889002717)
          ·
            refine ⟨12584407073657105208376019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33558418863085613889002717 12584407073657105208376019)
            ·
              refine ⟨18876610610485657812564029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12584407073657105208376019 18876610610485657812564029)
              ·
                refine ⟨7078728978932121679711511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18876610610485657812564029 7078728978932121679711511)
                ·
                  refine ⟨10618093468398182519567267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078728978932121679711511 10618093468398182519567267)
                  ·
                    refine ⟨15927140202597273779350901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10618093468398182519567267 15927140202597273779350901)
                    ·
                      refine ⟨1493169393993494416814147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15927140202597273779350901 1493169393993494416814147)
                      ·
                        rfl

theorem cell23_2907937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2907937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907937 prefixEnd_2907937 := by exact prefixLift 2907937
  have htrace : WordTrace (prefixWord ++ tailWord_2907937) baseStart_2907937 baseEnd_2907937 := by
    simpa [prefixWord, tailWord_2907937, baseEnd_2907937] using wordTrace_append hprefix tailTrace_2907937
  have hstable : (prefixWord ++ tailWord_2907937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907937).length < 2 ^ (prefixWord ++ tailWord_2907937).sum := by decide
  have hdescent : baseEnd_2907937 < baseStart_2907937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907944 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2907944 : Nat := 118140960795 + 2907944 * 2 ^ 59
def prefixEnd_2907944 : Nat := 4983230072969 + 3 ^ 40 * 2907944 * 2
def baseEnd_2907944 : Nat := 497724329452691963142205

theorem tailTrace_2907944 : CollatzResearch.WordTrace tailWord_2907944 prefixEnd_2907944 497724329452691963142205 := by
  unfold tailWord_2907944
  simp only [CollatzResearch.WordTrace]
  refine ⟨53030715488511500070497443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70707620651348666760663257 53030715488511500070497443)
  ·
    refine ⟨79546073232767250105746165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53030715488511500070497443 79546073232767250105746165)
    ·
      refine ⟨7457444365571929697413703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79546073232767250105746165 7457444365571929697413703)
      ·
        refine ⟨11186166548357894546120555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457444365571929697413703 11186166548357894546120555)
        ·
          refine ⟨16779249822536841819180833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11186166548357894546120555 16779249822536841819180833)
          ·
            refine ⟨12584437366902631364385625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16779249822536841819180833 12584437366902631364385625)
            ·
              refine ⟨9438328025176973523289219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12584437366902631364385625 9438328025176973523289219)
              ·
                refine ⟨14157492037765460284933829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438328025176973523289219 14157492037765460284933829)
                ·
                  refine ⟨2654529757081023803425093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14157492037765460284933829 2654529757081023803425093)
                  ·
                    refine ⟨497724329452691963142205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654529757081023803425093 497724329452691963142205)
                    ·
                      rfl

theorem cell23_2907944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2907944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907944 prefixEnd_2907944 := by exact prefixLift 2907944
  have htrace : WordTrace (prefixWord ++ tailWord_2907944) baseStart_2907944 baseEnd_2907944 := by
    simpa [prefixWord, tailWord_2907944, baseEnd_2907944] using wordTrace_append hprefix tailTrace_2907944
  have hstable : (prefixWord ++ tailWord_2907944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907944).length < 2 ^ (prefixWord ++ tailWord_2907944).sum := by decide
  have hdescent : baseEnd_2907944 < baseStart_2907944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907971 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 3]
def baseStart_2907971 : Nat := 118140960795 + 2907971 * 2 ^ 59
def prefixEnd_2907971 : Nat := 4983230072969 + 3 ^ 40 * 2907971 * 2
def baseEnd_2907971 : Nat := 1493186852335747283788991

theorem tailTrace_2907971 : CollatzResearch.WordTrace tailWord_2907971 prefixEnd_2907971 1493186852335747283788991 := by
  unfold tailWord_2907971
  simp only [CollatzResearch.WordTrace]
  refine ⟨106062415747925183752227767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70708277165283455834818511 106062415747925183752227767)
  ·
    refine ⟨159093623621887775628341651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106062415747925183752227767 159093623621887775628341651)
    ·
      refine ⟨238640435432831663442512477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159093623621887775628341651 238640435432831663442512477)
      ·
        refine ⟨89490163287311873790942179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238640435432831663442512477 89490163287311873790942179)
        ·
          refine ⟨134235244930967810686413269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89490163287311873790942179 134235244930967810686413269)
          ·
            refine ⟨3146138553069558062962811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134235244930967810686413269 3146138553069558062962811)
            ·
              refine ⟨4719207829604337094444217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146138553069558062962811 4719207829604337094444217)
              ·
                refine ⟨3539405872203252820833163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719207829604337094444217 3539405872203252820833163)
                ·
                  refine ⟨5309108808304879231249745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539405872203252820833163 5309108808304879231249745)
                  ·
                    refine ⟨3981831606228659423437309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5309108808304879231249745 3981831606228659423437309)
                    ·
                      refine ⟨1493186852335747283788991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981831606228659423437309 1493186852335747283788991)
                      ·
                        rfl

theorem cell23_2907971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_2907971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907971 prefixEnd_2907971 := by exact prefixLift 2907971
  have htrace : WordTrace (prefixWord ++ tailWord_2907971) baseStart_2907971 baseEnd_2907971 := by
    simpa [prefixWord, tailWord_2907971, baseEnd_2907971] using wordTrace_append hprefix tailTrace_2907971
  have hstable : (prefixWord ++ tailWord_2907971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907971).length < 2 ^ (prefixWord ++ tailWord_2907971).sum := by decide
  have hdescent : baseEnd_2907971 < baseStart_2907971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907981 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2907981 : Nat := 118140960795 + 2907981 * 2 ^ 59
def prefixEnd_2907981 : Nat := 4983230072969 + 3 ^ 40 * 2907981 * 2
def baseEnd_2907981 : Nat := 1493191987142292244663945

theorem tailTrace_2907981 : CollatzResearch.WordTrace tailWord_2907981 prefixEnd_2907981 1493191987142292244663945 := by
  unfold tailWord_2907981
  simp only [CollatzResearch.WordTrace]
  refine ⟨106062780477888955460091797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70708520318592636973394531 106062780477888955460091797)
  ·
    refine ⟨4971692834901044787191803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106062780477888955460091797 4971692834901044787191803)
    ·
      refine ⟨7457539252351567180787705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971692834901044787191803 7457539252351567180787705)
      ·
        refine ⟨5593154439263675385590779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7457539252351567180787705 5593154439263675385590779)
        ·
          refine ⟨8389731658895513078386169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593154439263675385590779 8389731658895513078386169)
          ·
            refine ⟨6292298744171634808789627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8389731658895513078386169 6292298744171634808789627)
            ·
              refine ⟨9438448116257452213184441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292298744171634808789627 9438448116257452213184441)
              ·
                refine ⟨7078836087193089159888331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9438448116257452213184441 7078836087193089159888331)
                ·
                  refine ⟨10618254130789633739832497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078836087193089159888331 10618254130789633739832497)
                  ·
                    refine ⟨7963690598092225304874373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10618254130789633739832497 7963690598092225304874373)
                    ·
                      refine ⟨1493191987142292244663945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7963690598092225304874373 1493191987142292244663945)
                      ·
                        rfl

theorem cell23_2907981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2907981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907981 prefixEnd_2907981 := by exact prefixLift 2907981
  have htrace : WordTrace (prefixWord ++ tailWord_2907981) baseStart_2907981 baseEnd_2907981 := by
    simpa [prefixWord, tailWord_2907981, baseEnd_2907981] using wordTrace_append hprefix tailTrace_2907981
  have hstable : (prefixWord ++ tailWord_2907981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907981).length < 2 ^ (prefixWord ++ tailWord_2907981).sum := by decide
  have hdescent : baseEnd_2907981 < baseStart_2907981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2907988 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_2907988 : Nat := 118140960795 + 2907988 * 2 ^ 59
def prefixEnd_2907988 : Nat := 4983230072969 + 3 ^ 40 * 2907988 * 2
def baseEnd_2907988 : Nat := 1493195581506873717276413

theorem tailTrace_2907988 : CollatzResearch.WordTrace tailWord_2907988 prefixEnd_2907988 1493195581506873717276413 := by
  unfold tailWord_2907988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53031517894431797827798309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70708690525909063770397745 53031517894431797827798309)
  ·
    refine ⟨9943409605205962092712183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53031517894431797827798309 9943409605205962092712183)
    ·
      refine ⟨14915114407808943139068275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9943409605205962092712183 14915114407808943139068275)
      ·
        refine ⟨22372671611713414708602413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915114407808943139068275 22372671611713414708602413)
        ·
          refine ⟨8389751854392530515725905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22372671611713414708602413 8389751854392530515725905)
          ·
            refine ⟨6292313890794397886794429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8389751854392530515725905 6292313890794397886794429)
            ·
              refine ⟨2359617709047899207547911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6292313890794397886794429 2359617709047899207547911)
              ·
                refine ⟨3539426563571848811321867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359617709047899207547911 3539426563571848811321867)
                ·
                  refine ⟨5309139845357773216982801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539426563571848811321867 5309139845357773216982801)
                  ·
                    refine ⟨3981854884018329912737101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5309139845357773216982801 3981854884018329912737101)
                    ·
                      refine ⟨1493195581506873717276413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981854884018329912737101 1493195581506873717276413)
                      ·
                        rfl

theorem cell23_2907988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_2907988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2907988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2907988 prefixEnd_2907988 := by exact prefixLift 2907988
  have htrace : WordTrace (prefixWord ++ tailWord_2907988) baseStart_2907988 baseEnd_2907988 := by
    simpa [prefixWord, tailWord_2907988, baseEnd_2907988] using wordTrace_append hprefix tailTrace_2907988
  have hstable : (prefixWord ++ tailWord_2907988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2907988).length < 2 ^ (prefixWord ++ tailWord_2907988).sum := by decide
  have hdescent : baseEnd_2907988 < baseStart_2907988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2907988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908001 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2908001 : Nat := 118140960795 + 2908001 * 2 ^ 59
def prefixEnd_2908001 : Nat := 4983230072969 + 3 ^ 40 * 2908001 * 2
def baseEnd_2908001 : Nat := 1493202256755382166413853

theorem tailTrace_2908001 : CollatzResearch.WordTrace tailWord_2908001 prefixEnd_2908001 1493202256755382166413853 := by
  unfold tailWord_2908001
  simp only [CollatzResearch.WordTrace]
  refine ⟨106063509937816498875819857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709006625210999250546571 106063509937816498875819857)
  ·
    refine ⟨79547632453362374156864893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106063509937816498875819857 79547632453362374156864893)
    ·
      refine ⟨29830362170010890308824335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79547632453362374156864893 29830362170010890308824335)
      ·
        refine ⟨44745543255016335463236503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29830362170010890308824335 44745543255016335463236503)
        ·
          refine ⟨67118314882524503194854755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44745543255016335463236503 67118314882524503194854755)
          ·
            refine ⟨100677472323786754792282133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67118314882524503194854755 100677472323786754792282133)
            ·
              refine ⟨4719256515177504130888225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100677472323786754792282133 4719256515177504130888225)
              ·
                refine ⟨3539442386383128098166169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719256515177504130888225 3539442386383128098166169)
                ·
                  refine ⟨2654581789787346073624627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539442386383128098166169 2654581789787346073624627)
                  ·
                    refine ⟨3981872684681019110436941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2654581789787346073624627 3981872684681019110436941)
                    ·
                      refine ⟨1493202256755382166413853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981872684681019110436941 1493202256755382166413853)
                      ·
                        rfl

theorem cell23_2908001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2908001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908001 prefixEnd_2908001 := by exact prefixLift 2908001
  have htrace : WordTrace (prefixWord ++ tailWord_2908001) baseStart_2908001 baseEnd_2908001 := by
    simpa [prefixWord, tailWord_2908001, baseEnd_2908001] using wordTrace_append hprefix tailTrace_2908001
  have hstable : (prefixWord ++ tailWord_2908001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908001).length < 2 ^ (prefixWord ++ tailWord_2908001).sum := by decide
  have hdescent : baseEnd_2908001 < baseStart_2908001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908002 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2908002 : Nat := 118140960795 + 2908002 * 2 ^ 59
def prefixEnd_2908002 : Nat := 4983230072969 + 3 ^ 40 * 2908002 * 2
def baseEnd_2908002 : Nat := 1493202770236036662501349

theorem tailTrace_2908002 : CollatzResearch.WordTrace tailWord_2908002 prefixEnd_2908002 1493202770236036662501349 := by
  unfold tailWord_2908002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515886602703219011651565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70709030940541917364404173 26515886602703219011651565)
  ·
    refine ⟨9943457476013707129369337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26515886602703219011651565 9943457476013707129369337)
    ·
      refine ⟨7457593107010280347027003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9943457476013707129369337 7457593107010280347027003)
      ·
        refine ⟨11186389660515420520540505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457593107010280347027003 11186389660515420520540505)
        ·
          refine ⟨8389792245386565390405379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11186389660515420520540505 8389792245386565390405379)
          ·
            refine ⟨12584688368079848085608069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8389792245386565390405379 12584688368079848085608069)
            ·
              refine ⟨2359629069014971516051513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12584688368079848085608069 2359629069014971516051513)
              ·
                refine ⟨1769721801761228637038635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359629069014971516051513 1769721801761228637038635)
                ·
                  refine ⟨2654582702641842955557953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769721801761228637038635 2654582702641842955557953)
                  ·
                    refine ⟨1990937026981382216668465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654582702641842955557953 1990937026981382216668465)
                    ·
                      refine ⟨1493202770236036662501349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990937026981382216668465 1493202770236036662501349)
                      ·
                        rfl

theorem cell23_2908002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2908002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908002 prefixEnd_2908002 := by exact prefixLift 2908002
  have htrace : WordTrace (prefixWord ++ tailWord_2908002) baseStart_2908002 baseEnd_2908002 := by
    simpa [prefixWord, tailWord_2908002, baseEnd_2908002] using wordTrace_append hprefix tailTrace_2908002
  have hstable : (prefixWord ++ tailWord_2908002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908002).length < 2 ^ (prefixWord ++ tailWord_2908002).sum := by decide
  have hdescent : baseEnd_2908002 < baseStart_2908002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908007 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2908007 : Nat := 118140960795 + 2908007 * 2 ^ 59
def prefixEnd_2908007 : Nat := 4983230072969 + 3 ^ 40 * 2908007 * 2
def baseEnd_2908007 : Nat := 1493205337639309142938825

theorem tailTrace_2908007 : CollatzResearch.WordTrace tailWord_2908007 prefixEnd_2908007 1493205337639309142938825 := by
  unfold tailWord_2908007
  simp only [CollatzResearch.WordTrace]
  refine ⟨106063728775794761900538275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709152517196507933692183 106063728775794761900538275)
  ·
    refine ⟨159095593163692142850807413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106063728775794761900538275 159095593163692142850807413)
    ·
      refine ⟨14915211859096138392263195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159095593163692142850807413 14915211859096138392263195)
      ·
        refine ⟨22372817788644207588394793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915211859096138392263195 22372817788644207588394793)
        ·
          refine ⟨16779613341483155691296095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22372817788644207588394793 16779613341483155691296095)
          ·
            refine ⟨25169420012224733536944143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16779613341483155691296095 25169420012224733536944143)
            ·
              refine ⟨37754130018337100305416215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25169420012224733536944143 37754130018337100305416215)
              ·
                refine ⟨56631195027505650458124323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37754130018337100305416215 56631195027505650458124323)
                ·
                  refine ⟨84946792541258475687186485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56631195027505650458124323 84946792541258475687186485)
                  ·
                    refine ⟨7963761800742982095673733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84946792541258475687186485 7963761800742982095673733)
                    ·
                      refine ⟨1493205337639309142938825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7963761800742982095673733 1493205337639309142938825)
                      ·
                        rfl

theorem cell23_2908007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2908007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908007 prefixEnd_2908007 := by exact prefixLift 2908007
  have htrace : WordTrace (prefixWord ++ tailWord_2908007) baseStart_2908007 baseEnd_2908007 := by
    simpa [prefixWord, tailWord_2908007, baseEnd_2908007] using wordTrace_append hprefix tailTrace_2908007
  have hstable : (prefixWord ++ tailWord_2908007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908007).length < 2 ^ (prefixWord ++ tailWord_2908007).sum := by decide
  have hdescent : baseEnd_2908007 < baseStart_2908007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908017 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_2908017 : Nat := 118140960795 + 2908017 * 2 ^ 59
def prefixEnd_2908017 : Nat := 4983230072969 + 3 ^ 40 * 2908017 * 2
def baseEnd_2908017 : Nat := 497736824148618034604593

theorem tailTrace_2908017 : CollatzResearch.WordTrace tailWord_2908017 prefixEnd_2908017 497736824148618034604593 := by
  unfold tailWord_2908017
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064093505758533608402305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709395670505689072268203 106064093505758533608402305)
  ·
    refine ⟨79548070129318900206301729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106064093505758533608402305 79548070129318900206301729)
    ·
      refine ⟨59661052596989175154726297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79548070129318900206301729 59661052596989175154726297)
      ·
        refine ⟨44745789447741881366044723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59661052596989175154726297 44745789447741881366044723)
        ·
          refine ⟨67118684171612822049067085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44745789447741881366044723 67118684171612822049067085)
          ·
            refine ⟨25169506564354808268400157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67118684171612822049067085 25169506564354808268400157)
            ·
              refine ⟨9438564961633053100650059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25169506564354808268400157 9438564961633053100650059)
              ·
                refine ⟨14157847442449579650975089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438564961633053100650059 14157847442449579650975089)
                ·
                  refine ⟨10618385581837184738231317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14157847442449579650975089 10618385581837184738231317)
                  ·
                    refine ⟨497736824148618034604593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10618385581837184738231317 497736824148618034604593)
                    ·
                      rfl

theorem cell23_2908017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_2908017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908017 prefixEnd_2908017 := by exact prefixLift 2908017
  have htrace : WordTrace (prefixWord ++ tailWord_2908017) baseStart_2908017 baseEnd_2908017 := by
    simpa [prefixWord, tailWord_2908017, baseEnd_2908017] using wordTrace_append hprefix tailTrace_2908017
  have hstable : (prefixWord ++ tailWord_2908017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908017).length < 2 ^ (prefixWord ++ tailWord_2908017).sum := by decide
  have hdescent : baseEnd_2908017 < baseStart_2908017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3]
def baseStart_2908027 : Nat := 118140960795 + 2908027 * 2 ^ 59
def prefixEnd_2908027 : Nat := 4983230072969 + 3 ^ 40 * 2908027 * 2
def baseEnd_2908027 : Nat := 1493215607252399064688733

theorem tailTrace_2908027 : CollatzResearch.WordTrace tailWord_2908027 prefixEnd_2908027 1493215607252399064688733 := by
  unfold tailWord_2908027
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064458235722305316266335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709638823814870210844223 106064458235722305316266335)
  ·
    refine ⟨159096687353583457974399503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106064458235722305316266335 159096687353583457974399503)
    ·
      refine ⟨238645031030375186961599255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159096687353583457974399503 238645031030375186961599255)
      ·
        refine ⟨357967546545562780442398883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238645031030375186961599255 357967546545562780442398883)
        ·
          refine ⟨536951319818344170663598325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357967546545562780442398883 536951319818344170663598325)
          ·
            refine ⟨50339186232969765999712343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 536951319818344170663598325 50339186232969765999712343)
            ·
              refine ⟨75508779349454648999568515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50339186232969765999712343 75508779349454648999568515)
              ·
                refine ⟨113263169024181973499352773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75508779349454648999568515 113263169024181973499352773)
                ·
                  refine ⟨21236844192034120031128645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113263169024181973499352773 21236844192034120031128645)
                  ·
                    refine ⟨3981908286006397505836621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21236844192034120031128645 3981908286006397505836621)
                    ·
                      refine ⟨1493215607252399064688733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3981908286006397505836621 1493215607252399064688733)
                      ·
                        rfl

theorem cell23_2908027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].length) (baseStart_2908027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908027 prefixEnd_2908027 := by exact prefixLift 2908027
  have htrace : WordTrace (prefixWord ++ tailWord_2908027) baseStart_2908027 baseEnd_2908027 := by
    simpa [prefixWord, tailWord_2908027, baseEnd_2908027] using wordTrace_append hprefix tailTrace_2908027
  have hstable : (prefixWord ++ tailWord_2908027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908027).length < 2 ^ (prefixWord ++ tailWord_2908027).sum := by decide
  have hdescent : baseEnd_2908027 < baseStart_2908027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908037 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2908037 : Nat := 118140960795 + 2908037 * 2 ^ 59
def prefixEnd_2908037 : Nat := 4983230072969 + 3 ^ 40 * 2908037 * 2
def baseEnd_2908037 : Nat := 1493220742058944025563687

theorem tailTrace_2908037 : CollatzResearch.WordTrace tailWord_2908037 prefixEnd_2908037 1493220742058944025563687 := by
  unfold tailWord_2908037
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064822965686077024130365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709881977124051349420243 106064822965686077024130365)
  ·
    refine ⟨39774308612132278884048887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106064822965686077024130365 39774308612132278884048887)
    ·
      refine ⟨59661462918198418326073331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39774308612132278884048887 59661462918198418326073331)
      ·
        refine ⟨89492194377297627489109997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59661462918198418326073331 89492194377297627489109997)
        ·
          refine ⟨33559572891486610308416249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89492194377297627489109997 33559572891486610308416249)
          ·
            refine ⟨25169679668614957731312187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33559572891486610308416249 25169679668614957731312187)
            ·
              refine ⟨37754519502922436596968281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25169679668614957731312187 37754519502922436596968281)
              ·
                refine ⟨28315889627191827447726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37754519502922436596968281 28315889627191827447726211)
                ·
                  refine ⟨42473834440787741171589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28315889627191827447726211 42473834440787741171589317)
                  ·
                    refine ⟨7963843957647701469672997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42473834440787741171589317 7963843957647701469672997)
                    ·
                      refine ⟨1493220742058944025563687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7963843957647701469672997 1493220742058944025563687)
                      ·
                        rfl

theorem cell23_2908037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2908037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908037 prefixEnd_2908037 := by exact prefixLift 2908037
  have htrace : WordTrace (prefixWord ++ tailWord_2908037) baseStart_2908037 baseEnd_2908037 := by
    simpa [prefixWord, tailWord_2908037, baseEnd_2908037] using wordTrace_append hprefix tailTrace_2908037
  have hstable : (prefixWord ++ tailWord_2908037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908037).length < 2 ^ (prefixWord ++ tailWord_2908037).sum := by decide
  have hdescent : baseEnd_2908037 < baseStart_2908037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908041 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 4, 2, 2]
def baseStart_2908041 : Nat := 118140960795 + 2908041 * 2 ^ 59
def prefixEnd_2908041 : Nat := 4983230072969 + 3 ^ 40 * 2908041 * 2
def baseEnd_2908041 : Nat := 1493222795981562009913669

theorem tailTrace_2908041 : CollatzResearch.WordTrace tailWord_2908041 prefixEnd_2908041 1493222795981562009913669 := by
  unfold tailWord_2908041
  simp only [CollatzResearch.WordTrace]
  refine ⟨106064968857671585707275977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70709979238447723804850651 106064968857671585707275977)
  ·
    refine ⟨79548726643253689280456983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106064968857671585707275977 79548726643253689280456983)
    ·
      refine ⟨119323089964880533920685475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79548726643253689280456983 119323089964880533920685475)
      ·
        refine ⟨178984634947320800881028213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119323089964880533920685475 178984634947320800881028213)
        ·
          refine ⟨16779809526311325082596395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178984634947320800881028213 16779809526311325082596395)
          ·
            refine ⟨25169714289466987623894593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16779809526311325082596395 25169714289466987623894593)
            ·
              refine ⟨18877285717100240717920945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25169714289466987623894593 18877285717100240717920945)
              ·
                refine ⟨14157964287825180538440709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18877285717100240717920945 14157964287825180538440709)
                ·
                  refine ⟨2654618303967221350957633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14157964287825180538440709 2654618303967221350957633)
                  ·
                    refine ⟨1990963727975416013218225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654618303967221350957633 1990963727975416013218225)
                    ·
                      refine ⟨1493222795981562009913669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990963727975416013218225 1493222795981562009913669)
                      ·
                        rfl

theorem cell23_2908041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2, 2].length) (baseStart_2908041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908041 prefixEnd_2908041 := by exact prefixLift 2908041
  have htrace : WordTrace (prefixWord ++ tailWord_2908041) baseStart_2908041 baseEnd_2908041 := by
    simpa [prefixWord, tailWord_2908041, baseEnd_2908041] using wordTrace_append hprefix tailTrace_2908041
  have hstable : (prefixWord ++ tailWord_2908041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908041).length < 2 ^ (prefixWord ++ tailWord_2908041).sum := by decide
  have hdescent : baseEnd_2908041 < baseStart_2908041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908058 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2908058 : Nat := 118140960795 + 2908058 * 2 ^ 59
def prefixEnd_2908058 : Nat := 4983230072969 + 3 ^ 40 * 2908058 * 2
def baseEnd_2908058 : Nat := 1493231525152688443401091

theorem tailTrace_2908058 : CollatzResearch.WordTrace tailWord_2908058 prefixEnd_2908058 1493231525152688443401091 := by
  unfold tailWord_2908058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26516397224652499402661207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70710392599073331740429885 26516397224652499402661207)
  ·
    refine ⟨39774595836978749103991811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26516397224652499402661207 39774595836978749103991811)
    ·
      refine ⟨59661893755468123655987717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39774595836978749103991811 59661893755468123655987717)
      ·
        refine ⟨11186605079150273185497697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59661893755468123655987717 11186605079150273185497697)
        ·
          refine ⟨8389953809362704889123273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11186605079150273185497697 8389953809362704889123273)
          ·
            refine ⟨6292465357022028666842455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8389953809362704889123273 6292465357022028666842455)
            ·
              refine ⟨9438698035533043000263683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292465357022028666842455 9438698035533043000263683)
              ·
                refine ⟨14158047053299564500395525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438698035533043000263683 14158047053299564500395525)
                ·
                  refine ⟨2654633822493668343824161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14158047053299564500395525 2654633822493668343824161)
                  ·
                    refine ⟨1990975366870251257868121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654633822493668343824161 1990975366870251257868121)
                    ·
                      refine ⟨1493231525152688443401091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1990975366870251257868121 1493231525152688443401091)
                      ·
                        rfl

theorem cell23_2908058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2908058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908058 prefixEnd_2908058 := by exact prefixLift 2908058
  have htrace : WordTrace (prefixWord ++ tailWord_2908058) baseStart_2908058 baseEnd_2908058 := by
    simpa [prefixWord, tailWord_2908058, baseEnd_2908058] using wordTrace_append hprefix tailTrace_2908058
  have hstable : (prefixWord ++ tailWord_2908058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908058).length < 2 ^ (prefixWord ++ tailWord_2908058).sum := by decide
  have hdescent : baseEnd_2908058 < baseStart_2908058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908087 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2908087 : Nat := 118140960795 + 2908087 * 2 ^ 59
def prefixEnd_2908087 : Nat := 4983230072969 + 3 ^ 40 * 2908087 * 2
def baseEnd_2908087 : Nat := 1493246416091668829938457

theorem tailTrace_2908087 : CollatzResearch.WordTrace tailWord_2908087 prefixEnd_2908087 1493246416091668829938457 := by
  unfold tailWord_2908087
  simp only [CollatzResearch.WordTrace]
  refine ⟨106066646615504935563450515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70711097743669957042300343 106066646615504935563450515)
  ·
    refine ⟨159099969923257403345175773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106066646615504935563450515 159099969923257403345175773)
    ·
      refine ⟨59662488721221526254440915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159099969923257403345175773 59662488721221526254440915)
      ·
        refine ⟨89493733081832289381661373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59662488721221526254440915 89493733081832289381661373)
        ·
          refine ⟨33560149905687108518123015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89493733081832289381661373 33560149905687108518123015)
          ·
            refine ⟨50340224858530662777184523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33560149905687108518123015 50340224858530662777184523)
            ·
              refine ⟨75510337287795994165776785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50340224858530662777184523 75510337287795994165776785)
              ·
                refine ⟨56632752965846995624332589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75510337287795994165776785 56632752965846995624332589)
                ·
                  refine ⟨21237282362192623359124721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56632752965846995624332589 21237282362192623359124721)
                  ·
                    refine ⟨15927961771644467519343541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21237282362192623359124721 15927961771644467519343541)
                    ·
                      refine ⟨1493246416091668829938457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15927961771644467519343541 1493246416091668829938457)
                      ·
                        rfl

theorem cell23_2908087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2908087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908087 prefixEnd_2908087 := by exact prefixLift 2908087
  have htrace : WordTrace (prefixWord ++ tailWord_2908087) baseStart_2908087 baseEnd_2908087 := by
    simpa [prefixWord, tailWord_2908087, baseEnd_2908087] using wordTrace_append hprefix tailTrace_2908087
  have hstable : (prefixWord ++ tailWord_2908087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908087).length < 2 ^ (prefixWord ++ tailWord_2908087).sum := by decide
  have hdescent : baseEnd_2908087 < baseStart_2908087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908094 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2908094 : Nat := 118140960795 + 2908094 * 2 ^ 59
def prefixEnd_2908094 : Nat := 4983230072969 + 3 ^ 40 * 2908094 * 2
def baseEnd_2908094 : Nat := 497750003485416767516975

theorem tailTrace_2908094 : CollatzResearch.WordTrace tailWord_2908094 prefixEnd_2908094 497750003485416767516975 := by
  unfold tailWord_2908094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258362740809946969869417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70711267950986383839303557 13258362740809946969869417)
  ·
    refine ⟨9943772055607460227402063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13258362740809946969869417 9943772055607460227402063)
    ·
      refine ⟨14915658083411190341103095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9943772055607460227402063 14915658083411190341103095)
      ·
        refine ⟨22373487125116785511654643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915658083411190341103095 22373487125116785511654643)
        ·
          refine ⟨33560230687675178267481965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22373487125116785511654643 33560230687675178267481965)
          ·
            refine ⟨12585086507878191850305737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33560230687675178267481965 12585086507878191850305737)
            ·
              refine ⟨9438814880908643887729303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12585086507878191850305737 9438814880908643887729303)
              ·
                refine ⟨14158222321362965831593955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9438814880908643887729303 14158222321362965831593955)
                ·
                  refine ⟨21237333482044448747390933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14158222321362965831593955 21237333482044448747390933)
                  ·
                    refine ⟨497750003485416767516975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21237333482044448747390933 497750003485416767516975)
                    ·
                      rfl

theorem cell23_2908094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2908094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908094 prefixEnd_2908094 := by exact prefixLift 2908094
  have htrace : WordTrace (prefixWord ++ tailWord_2908094) baseStart_2908094 baseEnd_2908094 := by
    simpa [prefixWord, tailWord_2908094, baseEnd_2908094] using wordTrace_append hprefix tailTrace_2908094
  have hstable : (prefixWord ++ tailWord_2908094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908094).length < 2 ^ (prefixWord ++ tailWord_2908094).sum := by decide
  have hdescent : baseEnd_2908094 < baseStart_2908094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908166 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2908166 : Nat := 118140960795 + 2908166 * 2 ^ 59
def prefixEnd_2908166 : Nat := 4983230072969 + 3 ^ 40 * 2908166 * 2
def baseEnd_2908166 : Nat := 165920775673708224538955

theorem tailTrace_2908166 : CollatzResearch.WordTrace tailWord_2908166 prefixEnd_2908166 165920775673708224538955 := by
  unfold tailWord_2908166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314672749444335376736761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70713018654812488037050901 3314672749444335376736761)
  ·
    refine ⟨2486004562083251532552571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3314672749444335376736761 2486004562083251532552571)
    ·
      refine ⟨3729006843124877298828857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486004562083251532552571 3729006843124877298828857)
      ·
        refine ⟨2796755132343657974121643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3729006843124877298828857 2796755132343657974121643)
        ·
          refine ⟨4195132698515486961182465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796755132343657974121643 4195132698515486961182465)
          ·
            refine ⟨3146349523886615220886849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195132698515486961182465 3146349523886615220886849)
            ·
              refine ⟨2359762142914961415665137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146349523886615220886849 2359762142914961415665137)
              ·
                refine ⟨1769821607186221061748853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359762142914961415665137 1769821607186221061748853)
                ·
                  refine ⟨165920775673708224538955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1769821607186221061748853 165920775673708224538955)
                  ·
                    rfl

theorem cell23_2908166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2908166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908166 prefixEnd_2908166 := by exact prefixLift 2908166
  have htrace : WordTrace (prefixWord ++ tailWord_2908166) baseStart_2908166 baseEnd_2908166 := by
    simpa [prefixWord, tailWord_2908166, baseEnd_2908166] using wordTrace_append hprefix tailTrace_2908166
  have hstable : (prefixWord ++ tailWord_2908166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908166).length < 2 ^ (prefixWord ++ tailWord_2908166).sum := by decide
  have hdescent : baseEnd_2908166 < baseStart_2908166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908174 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2908174 : Nat := 118140960795 + 2908174 * 2 ^ 59
def prefixEnd_2908174 : Nat := 4983230072969 + 3 ^ 40 * 2908174 * 2
def baseEnd_2908174 : Nat := 1493291088908609989550557

theorem tailTrace_2908174 : CollatzResearch.WordTrace tailWord_2908174 prefixEnd_2908174 1493291088908609989550557 := by
  unfold tailWord_2908174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258727470773718677733447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70713213177459832947911717 13258727470773718677733447)
  ·
    refine ⟨19888091206160578016600171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13258727470773718677733447 19888091206160578016600171)
    ·
      refine ⟨29832136809240867024900257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19888091206160578016600171 29832136809240867024900257)
      ·
        refine ⟨22374102606930650268675193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29832136809240867024900257 22374102606930650268675193)
        ·
          refine ⟨16780576955197987701506395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22374102606930650268675193 16780576955197987701506395)
          ·
            refine ⟨25170865432796981552259593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16780576955197987701506395 25170865432796981552259593)
            ·
              refine ⟨18878149074597736164194695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25170865432796981552259593 18878149074597736164194695)
              ·
                refine ⟨28317223611896604246292043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18878149074597736164194695 28317223611896604246292043)
                ·
                  refine ⟨42475835417844906369438065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28317223611896604246292043 42475835417844906369438065)
                  ·
                    refine ⟨31856876563383679777078549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42475835417844906369438065 31856876563383679777078549)
                    ·
                      refine ⟨1493291088908609989550557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31856876563383679777078549 1493291088908609989550557)
                      ·
                        rfl

theorem cell23_2908174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2908174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908174 prefixEnd_2908174 := by exact prefixLift 2908174
  have htrace : WordTrace (prefixWord ++ tailWord_2908174) baseStart_2908174 baseEnd_2908174 := by
    simpa [prefixWord, tailWord_2908174, baseEnd_2908174] using wordTrace_append hprefix tailTrace_2908174
  have hstable : (prefixWord ++ tailWord_2908174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908174).length < 2 ^ (prefixWord ++ tailWord_2908174).sum := by decide
  have hdescent : baseEnd_2908174 < baseStart_2908174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908184 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_2908184 : Nat := 118140960795 + 2908184 * 2 ^ 59
def prefixEnd_2908184 : Nat := 4983230072969 + 3 ^ 40 * 2908184 * 2
def baseEnd_2908184 : Nat := 497765407905051650141837

theorem tailTrace_2908184 : CollatzResearch.WordTrace tailWord_2908184 prefixEnd_2908184 497765407905051650141837 := by
  unfold tailWord_2908184
  simp only [CollatzResearch.WordTrace]
  refine ⟨53035092248076760564865803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70713456330769014086487737 53035092248076760564865803)
  ·
    refine ⟨79552638372115140847298705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53035092248076760564865803 79552638372115140847298705)
    ·
      refine ⟨59664478779086355635474029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79552638372115140847298705 59664478779086355635474029)
      ·
        refine ⟨22374179542157383363302761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59664478779086355635474029 22374179542157383363302761)
        ·
          refine ⟨16780634656618037522477071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22374179542157383363302761 16780634656618037522477071)
          ·
            refine ⟨25170951984927056283715607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16780634656618037522477071 25170951984927056283715607)
            ·
              refine ⟨37756427977390584425573411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25170951984927056283715607 37756427977390584425573411)
              ·
                refine ⟨56634641966085876638360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37756427977390584425573411 56634641966085876638360117)
                ·
                  refine ⟨5309497684320550934846261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56634641966085876638360117 5309497684320550934846261)
                  ·
                    refine ⟨497765407905051650141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5309497684320550934846261 497765407905051650141837)
                    ·
                      rfl

theorem cell23_2908184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_2908184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908184 prefixEnd_2908184 := by exact prefixLift 2908184
  have htrace : WordTrace (prefixWord ++ tailWord_2908184) baseStart_2908184 baseEnd_2908184 := by
    simpa [prefixWord, tailWord_2908184, baseEnd_2908184] using wordTrace_append hprefix tailTrace_2908184
  have hstable : (prefixWord ++ tailWord_2908184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908184).length < 2 ^ (prefixWord ++ tailWord_2908184).sum := by decide
  have hdescent : baseEnd_2908184 < baseStart_2908184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908191 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 5, 2]
def baseStart_2908191 : Nat := 118140960795 + 2908191 * 2 ^ 59
def prefixEnd_2908191 : Nat := 4983230072969 + 3 ^ 40 * 2908191 * 2
def baseEnd_2908191 : Nat := 1493299818079736423037979

theorem tailTrace_2908191 : CollatzResearch.WordTrace tailWord_2908191 prefixEnd_2908191 1493299818079736423037979 := by
  unfold tailWord_2908191
  simp only [CollatzResearch.WordTrace]
  refine ⟨106070439807128161325236427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70713626538085440883490951 106070439807128161325236427)
  ·
    refine ⟨159105659710692241987854641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106070439807128161325236427 159105659710692241987854641)
    ·
      refine ⟨119329244783019181490890981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159105659710692241987854641 119329244783019181490890981)
      ·
        refine ⟨22374233396816096529542059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119329244783019181490890981 22374233396816096529542059)
        ·
          refine ⟨33561350095224144794313089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22374233396816096529542059 33561350095224144794313089)
          ·
            refine ⟨25171012571418108595734817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33561350095224144794313089 25171012571418108595734817)
            ·
              refine ⟨18878259428563581446801113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25171012571418108595734817 18878259428563581446801113)
              ·
                refine ⟨14158694571422686085100835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18878259428563581446801113 14158694571422686085100835)
                ·
                  refine ⟨21238041857134029127651253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14158694571422686085100835 21238041857134029127651253)
                  ·
                    refine ⟨1991066424106315230717305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21238041857134029127651253 1991066424106315230717305)
                    ·
                      refine ⟨1493299818079736423037979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991066424106315230717305 1493299818079736423037979)
                      ·
                        rfl

theorem cell23_2908191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_2908191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908191 prefixEnd_2908191 := by exact prefixLift 2908191
  have htrace : WordTrace (prefixWord ++ tailWord_2908191) baseStart_2908191 baseEnd_2908191 := by
    simpa [prefixWord, tailWord_2908191, baseEnd_2908191] using wordTrace_append hprefix tailTrace_2908191
  have hstable : (prefixWord ++ tailWord_2908191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908191).length < 2 ^ (prefixWord ++ tailWord_2908191).sum := by decide
  have hdescent : baseEnd_2908191 < baseStart_2908191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908194 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2908194 : Nat := 118140960795 + 2908194 * 2 ^ 59
def prefixEnd_2908194 : Nat := 4983230072969 + 3 ^ 40 * 2908194 * 2
def baseEnd_2908194 : Nat := 1493301358521699911300465

theorem tailTrace_2908194 : CollatzResearch.WordTrace tailWord_2908194 prefixEnd_2908194 1493301358521699911300465 := by
  unfold tailWord_2908194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26517637306529323209398909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70713699484078195225063757 26517637306529323209398909)
  ·
    refine ⟨9944113989948496203524591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26517637306529323209398909 9944113989948496203524591)
    ·
      refine ⟨14916170984922744305286887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944113989948496203524591 14916170984922744305286887)
      ·
        refine ⟨22374256477384116457930331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14916170984922744305286887 22374256477384116457930331)
        ·
          refine ⟨33561384716076174686895497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22374256477384116457930331 33561384716076174686895497)
          ·
            refine ⟨25171038537057131015171623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33561384716076174686895497 25171038537057131015171623)
            ·
              refine ⟨37756557805585696522757435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25171038537057131015171623 37756557805585696522757435)
              ·
                refine ⟨56634836708378544784136153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37756557805585696522757435 56634836708378544784136153)
                ·
                  refine ⟨42476127531283908588102115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56634836708378544784136153 42476127531283908588102115)
                  ·
                    refine ⟨63714191296925862882153173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42476127531283908588102115 63714191296925862882153173)
                    ·
                      refine ⟨1493301358521699911300465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63714191296925862882153173 1493301358521699911300465)
                      ·
                        rfl

theorem cell23_2908194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2908194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908194 prefixEnd_2908194 := by exact prefixLift 2908194
  have htrace : WordTrace (prefixWord ++ tailWord_2908194) baseStart_2908194 baseEnd_2908194 := by
    simpa [prefixWord, tailWord_2908194, baseEnd_2908194] using wordTrace_append hprefix tailTrace_2908194
  have hstable : (prefixWord ++ tailWord_2908194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908194).length < 2 ^ (prefixWord ++ tailWord_2908194).sum := by decide
  have hdescent : baseEnd_2908194 < baseStart_2908194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908208 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2]
def baseStart_2908208 : Nat := 118140960795 + 2908208 * 2 ^ 59
def prefixEnd_2908208 : Nat := 4983230072969 + 3 ^ 40 * 2908208 * 2
def baseEnd_2908208 : Nat := 1493308547250862856525401

theorem tailTrace_2908208 : CollatzResearch.WordTrace tailWord_2908208 prefixEnd_2908208 1493308547250862856525401 := by
  unfold tailWord_2908208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53035529924033286614302639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70714039898711048819070185 53035529924033286614302639)
  ·
    refine ⟨79553294886049929921453959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53035529924033286614302639 79553294886049929921453959)
    ·
      refine ⟨119329942329074894882180939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79553294886049929921453959 119329942329074894882180939)
      ·
        refine ⟨178994913493612342323271409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119329942329074894882180939 178994913493612342323271409)
        ·
          refine ⟨134246185120209256742453557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178994913493612342323271409 134246185120209256742453557)
          ·
            refine ⟨12585579855019617819605021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134246185120209256742453557 12585579855019617819605021)
            ·
              refine ⟨4719592445632356682351883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12585579855019617819605021 4719592445632356682351883)
              ·
                refine ⟨7079388668448535023527825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719592445632356682351883 7079388668448535023527825)
                ·
                  refine ⟨5309541501336401267645869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7079388668448535023527825 5309541501336401267645869)
                  ·
                    refine ⟨1991078063001150475367201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5309541501336401267645869 1991078063001150475367201)
                    ·
                      refine ⟨1493308547250862856525401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991078063001150475367201 1493308547250862856525401)
                      ·
                        rfl

theorem cell23_2908208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2].length) (baseStart_2908208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908208 prefixEnd_2908208 := by exact prefixLift 2908208
  have htrace : WordTrace (prefixWord ++ tailWord_2908208) baseStart_2908208 baseEnd_2908208 := by
    simpa [prefixWord, tailWord_2908208, baseEnd_2908208] using wordTrace_append hprefix tailTrace_2908208
  have hstable : (prefixWord ++ tailWord_2908208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908208).length < 2 ^ (prefixWord ++ tailWord_2908208).sum := by decide
  have hdescent : baseEnd_2908208 < baseStart_2908208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908231 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 4, 4]
def baseStart_2908231 : Nat := 118140960795 + 2908231 * 2 ^ 59
def prefixEnd_2908231 : Nat := 4983230072969 + 3 ^ 40 * 2908231 * 2
def baseEnd_2908231 : Nat := 497773452435305422179265

theorem tailTrace_2908231 : CollatzResearch.WordTrace tailWord_2908231 prefixEnd_2908231 497773452435305422179265 := by
  unfold tailWord_2908231
  simp only [CollatzResearch.WordTrace]
  refine ⟨106071898726983248156692547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70714599151322165437795031 106071898726983248156692547)
  ·
    refine ⟨159107848090474872235038821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106071898726983248156692547 159107848090474872235038821)
    ·
      refine ⟨29832721516964038544069779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159107848090474872235038821 29832721516964038544069779)
      ·
        refine ⟨44749082275446057816104669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29832721516964038544069779 44749082275446057816104669)
        ·
          refine ⟨16780905853292271681039251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44749082275446057816104669 16780905853292271681039251)
          ·
            refine ⟨25171358779938407521558877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16780905853292271681039251 25171358779938407521558877)
            ·
              refine ⟨9439259542476902820584579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25171358779938407521558877 9439259542476902820584579)
              ·
                refine ⟨14158889313715354230876869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439259542476902820584579 14158889313715354230876869)
                ·
                  refine ⟨2654791746321628918289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14158889313715354230876869 2654791746321628918289413)
                  ·
                    refine ⟨497773452435305422179265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654791746321628918289413 497773452435305422179265)
                    ·
                      rfl

theorem cell23_2908231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_2908231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908231 prefixEnd_2908231 := by exact prefixLift 2908231
  have htrace : WordTrace (prefixWord ++ tailWord_2908231) baseStart_2908231 baseEnd_2908231 := by
    simpa [prefixWord, tailWord_2908231, baseEnd_2908231] using wordTrace_append hprefix tailTrace_2908231
  have hstable : (prefixWord ++ tailWord_2908231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908231).length < 2 ^ (prefixWord ++ tailWord_2908231).sum := by decide
  have hdescent : baseEnd_2908231 < baseStart_2908231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908234 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2908234 : Nat := 118140960795 + 2908234 * 2 ^ 59
def prefixEnd_2908234 : Nat := 4983230072969 + 3 ^ 40 * 2908234 * 2
def baseEnd_2908234 : Nat := 1493321897747879754800281

theorem tailTrace_2908234 : CollatzResearch.WordTrace tailWord_2908234 prefixEnd_2908234 1493321897747879754800281 := by
  unfold tailWord_2908234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518002036493094917262939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70714672097314919779367837 26518002036493094917262939)
  ·
    refine ⟨39777003054739642375894409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26518002036493094917262939 39777003054739642375894409)
    ·
      refine ⟨29832752291054731781920807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39777003054739642375894409 29832752291054731781920807)
      ·
        refine ⟨44749128436582097672881211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29832752291054731781920807 44749128436582097672881211)
        ·
          refine ⟨67123692654873146509321817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44749128436582097672881211 67123692654873146509321817)
          ·
            refine ⟨50342769491154859881991363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67123692654873146509321817 50342769491154859881991363)
            ·
              refine ⟨75514154236732289822987045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50342769491154859881991363 75514154236732289822987045)
              ·
                refine ⟨14158903919387304341810071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75514154236732289822987045 14158903919387304341810071)
                ·
                  refine ⟨21238355879080956512715107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14158903919387304341810071 21238355879080956512715107)
                  ·
                    refine ⟨31857533818621434769072661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21238355879080956512715107 31857533818621434769072661)
                    ·
                      refine ⟨1493321897747879754800281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31857533818621434769072661 1493321897747879754800281)
                      ·
                        rfl

theorem cell23_2908234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2908234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908234 prefixEnd_2908234 := by exact prefixLift 2908234
  have htrace : WordTrace (prefixWord ++ tailWord_2908234) baseStart_2908234 baseEnd_2908234 := by
    simpa [prefixWord, tailWord_2908234, baseEnd_2908234] using wordTrace_append hprefix tailTrace_2908234
  have hstable : (prefixWord ++ tailWord_2908234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908234).length < 2 ^ (prefixWord ++ tailWord_2908234).sum := by decide
  have hdescent : baseEnd_2908234 < baseStart_2908234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908244 : List Nat := [2, 4, 1, 1, 1, 1, 1, 12]
def baseStart_2908244 : Nat := 118140960795 + 2908244 * 2 ^ 59
def prefixEnd_2908244 : Nat := 4983230072969 + 3 ^ 40 * 2908244 * 2
def baseEnd_2908244 : Nat := 55308408613126841321305

theorem tailTrace_2908244 : CollatzResearch.WordTrace tailWord_2908244 prefixEnd_2908244 55308408613126841321305 := by
  unfold tailWord_2908244
  simp only [CollatzResearch.WordTrace]
  refine ⟨53036186437968075688457893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70714915250624100917943857 53036186437968075688457893)
  ·
    refine ⟨9944284957119014191585855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53036186437968075688457893 9944284957119014191585855)
    ·
      refine ⟨14916427435678521287378783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944284957119014191585855 14916427435678521287378783)
      ·
        refine ⟨22374641153517781931068175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14916427435678521287378783 22374641153517781931068175)
        ·
          refine ⟨33561961730276672896602263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22374641153517781931068175 33561961730276672896602263)
          ·
            refine ⟨50342942595415009344903395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33561961730276672896602263 50342942595415009344903395)
            ·
              refine ⟨75514413893122514017355093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50342942595415009344903395 75514413893122514017355093)
              ·
                refine ⟨55308408613126841321305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 75514413893122514017355093 55308408613126841321305)
                ·
                  rfl

theorem cell23_2908244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 12].length) (baseStart_2908244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908244 prefixEnd_2908244 := by exact prefixLift 2908244
  have htrace : WordTrace (prefixWord ++ tailWord_2908244) baseStart_2908244 baseEnd_2908244 := by
    simpa [prefixWord, tailWord_2908244, baseEnd_2908244] using wordTrace_append hprefix tailTrace_2908244
  have hstable : (prefixWord ++ tailWord_2908244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908244).length < 2 ^ (prefixWord ++ tailWord_2908244).sum := by decide
  have hdescent : baseEnd_2908244 < baseStart_2908244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908261 : List Nat := [1, 3, 1, 3, 2, 2, 4, 7]
def baseStart_2908261 : Nat := 118140960795 + 2908261 * 2 ^ 59
def prefixEnd_2908261 : Nat := 4983230072969 + 3 ^ 40 * 2908261 * 2
def baseEnd_2908261 : Nat := 55308731915761153672691

theorem tailTrace_2908261 : CollatzResearch.WordTrace tailWord_2908261 prefixEnd_2908261 55308731915761153672691 := by
  unfold tailWord_2908261
  simp only [CollatzResearch.WordTrace]
  refine ⟨106072992916874563280284637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70715328611249708853523091 106072992916874563280284637)
  ·
    refine ⟨39777372343827961230106739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106072992916874563280284637 39777372343827961230106739)
    ·
      refine ⟨59666058515741941845160109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39777372343827961230106739 59666058515741941845160109)
      ·
        refine ⟨22374771943403228191935041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59666058515741941845160109 22374771943403228191935041)
        ·
          refine ⟨16781078957552421143951281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22374771943403228191935041 16781078957552421143951281)
          ·
            refine ⟨12585809218164315857963461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16781078957552421143951281 12585809218164315857963461)
            ·
              refine ⟨2359839228405809223368149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12585809218164315857963461 2359839228405809223368149)
              ·
                refine ⟨55308731915761153672691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2359839228405809223368149 55308731915761153672691)
                ·
                  rfl

theorem cell23_2908261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 7].length) (baseStart_2908261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908261 prefixEnd_2908261 := by exact prefixLift 2908261
  have htrace : WordTrace (prefixWord ++ tailWord_2908261) baseStart_2908261 baseEnd_2908261 := by
    simpa [prefixWord, tailWord_2908261, baseEnd_2908261] using wordTrace_append hprefix tailTrace_2908261
  have hstable : (prefixWord ++ tailWord_2908261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908261).length < 2 ^ (prefixWord ++ tailWord_2908261).sum := by decide
  have hdescent : baseEnd_2908261 < baseStart_2908261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908272 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 1, 2, 2]
def baseStart_2908272 : Nat := 118140960795 + 2908272 * 2 ^ 59
def prefixEnd_2908272 : Nat := 4983230072969 + 3 ^ 40 * 2908272 * 2
def baseEnd_2908272 : Nat := 1493341410012750606125107

theorem tailTrace_2908272 : CollatzResearch.WordTrace tailWord_2908272 prefixEnd_2908272 1493341410012750606125107 := by
  unfold tailWord_2908272
  simp only [CollatzResearch.WordTrace]
  refine ⟨53036697059917356079467535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70715596079889808105956713 53036697059917356079467535)
  ·
    refine ⟨79555045589876034119201303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53036697059917356079467535 79555045589876034119201303)
    ·
      refine ⟨119332568384814051178801955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79555045589876034119201303 119332568384814051178801955)
      ·
        refine ⟨178998852577221076768202933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119332568384814051178801955 178998852577221076768202933)
        ·
          refine ⟨16781142429114475947019025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178998852577221076768202933 16781142429114475947019025)
          ·
            refine ⟨12585856821835856960264269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16781142429114475947019025 12585856821835856960264269)
            ·
              refine ⟨4719696308188446360099101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12585856821835856960264269 4719696308188446360099101)
              ·
                refine ⟨1769886115570667385037163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4719696308188446360099101 1769886115570667385037163)
                ·
                  refine ⟨2654829173356001077555745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769886115570667385037163 2654829173356001077555745)
                  ·
                    refine ⟨1991121880017000808166809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654829173356001077555745 1991121880017000808166809)
                    ·
                      refine ⟨1493341410012750606125107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991121880017000808166809 1493341410012750606125107)
                      ·
                        rfl

theorem cell23_2908272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 2, 2].length) (baseStart_2908272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908272 prefixEnd_2908272 := by exact prefixLift 2908272
  have htrace : WordTrace (prefixWord ++ tailWord_2908272) baseStart_2908272 baseEnd_2908272 := by
    simpa [prefixWord, tailWord_2908272, baseEnd_2908272] using wordTrace_append hprefix tailTrace_2908272
  have hstable : (prefixWord ++ tailWord_2908272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908272).length < 2 ^ (prefixWord ++ tailWord_2908272).sum := by decide
  have hdescent : baseEnd_2908272 < baseStart_2908272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908288 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_2908288 : Nat := 118140960795 + 2908288 * 2 ^ 59
def prefixEnd_2908288 : Nat := 4983230072969 + 3 ^ 40 * 2908288 * 2
def baseEnd_2908288 : Nat := 1493349625703222543525033

theorem tailTrace_2908288 : CollatzResearch.WordTrace tailWord_2908288 prefixEnd_2908288 1493349625703222543525033 := by
  unfold tailWord_2908288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53036988843888373445758759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70715985125184497927678345 53036988843888373445758759)
  ·
    refine ⟨79555483265832560168638139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53036988843888373445758759 79555483265832560168638139)
    ·
      refine ⟨119333224898748840252957209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79555483265832560168638139 119333224898748840252957209)
      ·
        refine ⟨89499918674061630189717907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119333224898748840252957209 89499918674061630189717907)
        ·
          refine ⟨134249878011092445284576861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89499918674061630189717907 134249878011092445284576861)
          ·
            refine ⟨50343704254159666981716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134249878011092445284576861 50343704254159666981716323)
            ·
              refine ⟨75515556381239500472574485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50343704254159666981716323 75515556381239500472574485)
              ·
                refine ⟨3539791705370601584651929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75515556381239500472574485 3539791705370601584651929)
                ·
                  refine ⟨2654843779027951188488947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539791705370601584651929 2654843779027951188488947)
                  ·
                    refine ⟨3982265668541926782733421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2654843779027951188488947 3982265668541926782733421)
                    ·
                      refine ⟨1493349625703222543525033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3982265668541926782733421 1493349625703222543525033)
                      ·
                        rfl

theorem cell23_2908288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_2908288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908288 prefixEnd_2908288 := by exact prefixLift 2908288
  have htrace : WordTrace (prefixWord ++ tailWord_2908288) baseStart_2908288 baseEnd_2908288 := by
    simpa [prefixWord, tailWord_2908288, baseEnd_2908288] using wordTrace_append hprefix tailTrace_2908288
  have hstable : (prefixWord ++ tailWord_2908288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908288).length < 2 ^ (prefixWord ++ tailWord_2908288).sum := by decide
  have hdescent : baseEnd_2908288 < baseStart_2908288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908289 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2908289 : Nat := 118140960795 + 2908289 * 2 ^ 59
def prefixEnd_2908289 : Nat := 4983230072969 + 3 ^ 40 * 2908289 * 2
def baseEnd_2908289 : Nat := 1493350139183877039612529

theorem tailTrace_2908289 : CollatzResearch.WordTrace tailWord_2908289 prefixEnd_2908289 1493350139183877039612529 := by
  unfold tailWord_2908289
  simp only [CollatzResearch.WordTrace]
  refine ⟨106074014160773124062303921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70716009440515416041535947 106074014160773124062303921)
  ·
    refine ⟨79555510620579843046727941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106074014160773124062303921 79555510620579843046727941)
    ·
      refine ⟨14916658241358720571261489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79555510620579843046727941 14916658241358720571261489)
      ·
        refine ⟨11187493681019040428446117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14916658241358720571261489 11187493681019040428446117)
        ·
          refine ⟨2097655065191070080333647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11187493681019040428446117 2097655065191070080333647)
          ·
            refine ⟨3146482597786605120500471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097655065191070080333647 3146482597786605120500471)
            ·
              refine ⟨4719723896679907680750707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146482597786605120500471 4719723896679907680750707)
              ·
                refine ⟨7079585845019861521126061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719723896679907680750707 7079585845019861521126061)
                ·
                  refine ⟨2654844691882448070422273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7079585845019861521126061 2654844691882448070422273)
                  ·
                    refine ⟨1991133518911836052816705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654844691882448070422273 1991133518911836052816705)
                    ·
                      refine ⟨1493350139183877039612529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991133518911836052816705 1493350139183877039612529)
                      ·
                        rfl

theorem cell23_2908289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2908289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908289 prefixEnd_2908289 := by exact prefixLift 2908289
  have htrace : WordTrace (prefixWord ++ tailWord_2908289) baseStart_2908289 baseEnd_2908289 := by
    simpa [prefixWord, tailWord_2908289, baseEnd_2908289] using wordTrace_append hprefix tailTrace_2908289
  have hstable : (prefixWord ++ tailWord_2908289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908289).length < 2 ^ (prefixWord ++ tailWord_2908289).sum := by decide
  have hdescent : baseEnd_2908289 < baseStart_2908289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908304 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_2908304 : Nat := 118140960795 + 2908304 * 2 ^ 59
def prefixEnd_2908304 : Nat := 4983230072969 + 3 ^ 40 * 2908304 * 2
def baseEnd_2908304 : Nat := 497785947131231493641653

theorem tailTrace_2908304 : CollatzResearch.WordTrace tailWord_2908304 prefixEnd_2908304 497785947131231493641653 := by
  unfold tailWord_2908304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53037280627859390812049983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70716374170479187749399977 53037280627859390812049983)
  ·
    refine ⟨79555920941789086218074975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53037280627859390812049983 79555920941789086218074975)
    ·
      refine ⟨119333881412683629327112463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79555920941789086218074975 119333881412683629327112463)
      ·
        refine ⟨179000822119025443990668695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119333881412683629327112463 179000822119025443990668695)
        ·
          refine ⟨268501233178538165986003043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179000822119025443990668695 268501233178538165986003043)
          ·
            refine ⟨402751849767807248979004565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268501233178538165986003043 402751849767807248979004565)
            ·
              refine ⟨18878992957865964795890839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 402751849767807248979004565 18878992957865964795890839)
              ·
                refine ⟨28318489436798947193836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18878992957865964795890839 28318489436798947193836259)
                ·
                  refine ⟨42477734155198420790754389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28318489436798947193836259 42477734155198420790754389)
                  ·
                    refine ⟨497785947131231493641653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42477734155198420790754389 497785947131231493641653)
                    ·
                      rfl

theorem cell23_2908304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_2908304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908304 prefixEnd_2908304 := by exact prefixLift 2908304
  have htrace : WordTrace (prefixWord ++ tailWord_2908304) baseStart_2908304 baseEnd_2908304 := by
    simpa [prefixWord, tailWord_2908304, baseEnd_2908304] using wordTrace_append hprefix tailTrace_2908304
  have hstable : (prefixWord ++ tailWord_2908304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908304).length < 2 ^ (prefixWord ++ tailWord_2908304).sum := by decide
  have hdescent : baseEnd_2908304 < baseStart_2908304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908428 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_2908428 : Nat := 118140960795 + 2908428 * 2 ^ 59
def prefixEnd_2908428 : Nat := 4983230072969 + 3 ^ 40 * 2908428 * 2
def baseEnd_2908428 : Nat := 497807170998283998591463

theorem tailTrace_2908428 : CollatzResearch.WordTrace tailWord_2908428 prefixEnd_2908428 497807170998283998591463 := by
  unfold tailWord_2908428
  simp only [CollatzResearch.WordTrace]
  refine ⟨53039541953634775400806969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70719389271513033867742625 53039541953634775400806969)
  ·
    refine ⟨39779656465226081550605227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53039541953634775400806969 39779656465226081550605227)
    ·
      refine ⟨59669484697839122325907841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39779656465226081550605227 59669484697839122325907841)
      ·
        refine ⟨44752113523379341744430881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59669484697839122325907841 44752113523379341744430881)
        ·
          refine ⟨33564085142534506308323161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44752113523379341744430881 33564085142534506308323161)
          ·
            refine ⟨25173063856900879731242371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33564085142534506308323161 25173063856900879731242371)
            ·
              refine ⟨37759595785351319596863557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25173063856900879731242371 37759595785351319596863557)
              ·
                refine ⟨7079924209753372424411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37759595785351319596863557 7079924209753372424411917)
                ·
                  refine ⟨2654971578657514659154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7079924209753372424411917 2654971578657514659154469)
                  ·
                    refine ⟨497807170998283998591463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2654971578657514659154469 497807170998283998591463)
                    ·
                      rfl

theorem cell23_2908428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_2908428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908428 prefixEnd_2908428 := by exact prefixLift 2908428
  have htrace : WordTrace (prefixWord ++ tailWord_2908428) baseStart_2908428 baseEnd_2908428 := by
    simpa [prefixWord, tailWord_2908428, baseEnd_2908428] using wordTrace_append hprefix tailTrace_2908428
  have hstable : (prefixWord ++ tailWord_2908428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908428).length < 2 ^ (prefixWord ++ tailWord_2908428).sum := by decide
  have hdescent : baseEnd_2908428 < baseStart_2908428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908519 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_2908519 : Nat := 118140960795 + 2908519 * 2 ^ 59
def prefixEnd_2908519 : Nat := 4983230072969 + 3 ^ 40 * 2908519 * 2
def baseEnd_2908519 : Nat := 1493468239734411139736471

theorem tailTrace_2908519 : CollatzResearch.WordTrace tailWord_2908519 prefixEnd_2908519 1493468239734411139736471 := by
  unfold tailWord_2908519
  simp only [CollatzResearch.WordTrace]
  refine ⟨106082402949939873343176611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70721601966626582228784407 106082402949939873343176611)
  ·
    refine ⟨159123604424909810014764917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106082402949939873343176611 159123604424909810014764917)
    ·
      refine ⟨14917837914835294688884211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159123604424909810014764917 14917837914835294688884211)
      ·
        refine ⟨22376756872252942033326317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14917837914835294688884211 22376756872252942033326317)
        ·
          refine ⟨8391283827094853262497369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22376756872252942033326317 8391283827094853262497369)
          ·
            refine ⟨6293462870321139946873027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8391283827094853262497369 6293462870321139946873027)
            ·
              refine ⟨9440194305481709920309541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6293462870321139946873027 9440194305481709920309541)
              ·
                refine ⟨1770036432277820610058039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9440194305481709920309541 1770036432277820610058039)
                ·
                  refine ⟨2655054648416730915087059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770036432277820610058039 2655054648416730915087059)
                  ·
                    refine ⟨3982581972625096372630589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655054648416730915087059 3982581972625096372630589)
                    ·
                      refine ⟨1493468239734411139736471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3982581972625096372630589 1493468239734411139736471)
                      ·
                        rfl

theorem cell23_2908519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_2908519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908519 prefixEnd_2908519 := by exact prefixLift 2908519
  have htrace : WordTrace (prefixWord ++ tailWord_2908519) baseStart_2908519 baseEnd_2908519 := by
    simpa [prefixWord, tailWord_2908519, baseEnd_2908519] using wordTrace_append hprefix tailTrace_2908519
  have hstable : (prefixWord ++ tailWord_2908519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908519).length < 2 ^ (prefixWord ++ tailWord_2908519).sum := by decide
  have hdescent : baseEnd_2908519 < baseStart_2908519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908585 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 5, 3, 2]
def baseStart_2908585 : Nat := 118140960795 + 2908585 * 2 ^ 59
def prefixEnd_2908585 : Nat := 4983230072969 + 3 ^ 40 * 2908585 * 2
def baseEnd_2908585 : Nat := 1493502129457607881511167

theorem tailTrace_2908585 : CollatzResearch.WordTrace tailWord_2908585 prefixEnd_2908585 1493502129457607881511167 := by
  unfold tailWord_2908585
  simp only [CollatzResearch.WordTrace]
  refine ⟨106084810167700766615079209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70723206778467177743386139 106084810167700766615079209)
  ·
    refine ⟨79563607625775574961309407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106084810167700766615079209 79563607625775574961309407)
    ·
      refine ⟨119345411438663362441964111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79563607625775574961309407 119345411438663362441964111)
      ·
        refine ⟨179018117157995043662946167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119345411438663362441964111 179018117157995043662946167)
        ·
          refine ⟨268527175736992565494419251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179018117157995043662946167 268527175736992565494419251)
          ·
            refine ⟨402790763605488848241628877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268527175736992565494419251 402790763605488848241628877)
            ·
              refine ⟨151046536352058318090610829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402790763605488848241628877 151046536352058318090610829)
              ·
                refine ⟨56642451132021869283979061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151046536352058318090610829 56642451132021869283979061)
                ·
                  refine ⟨5310229793627050245373037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56642451132021869283979061 5310229793627050245373037)
                  ·
                    refine ⟨1991336172610143842014889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5310229793627050245373037 1991336172610143842014889)
                    ·
                      refine ⟨1493502129457607881511167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991336172610143842014889 1493502129457607881511167)
                      ·
                        rfl

theorem cell23_2908585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3, 2].length) (baseStart_2908585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908585 prefixEnd_2908585 := by exact prefixLift 2908585
  have htrace : WordTrace (prefixWord ++ tailWord_2908585) baseStart_2908585 baseEnd_2908585 := by
    simpa [prefixWord, tailWord_2908585, baseEnd_2908585] using wordTrace_append hprefix tailTrace_2908585
  have hstable : (prefixWord ++ tailWord_2908585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908585).length < 2 ^ (prefixWord ++ tailWord_2908585).sum := by decide
  have hdescent : baseEnd_2908585 < baseStart_2908585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908586 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2908586 : Nat := 118140960795 + 2908586 * 2 ^ 59
def prefixEnd_2908586 : Nat := 4983230072969 + 3 ^ 40 * 2908586 * 2
def baseEnd_2908586 : Nat := 497834214312754125866221

theorem tailTrace_2908586 : CollatzResearch.WordTrace tailWord_2908586 prefixEnd_2908586 497834214312754125866221 := by
  unfold tailWord_2908586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521211660174285946466403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70723231093798095857243741 26521211660174285946466403)
  ·
    refine ⟨39781817490261428919699605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26521211660174285946466403 39781817490261428919699605)
    ·
      refine ⟨1864772694856004480610919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39781817490261428919699605 1864772694856004480610919)
      ·
        refine ⟨2797159042284006720916379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864772694856004480610919 2797159042284006720916379)
        ·
          refine ⟨4195738563426010081374569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797159042284006720916379 4195738563426010081374569)
          ·
            refine ⟨3146803922569507561030927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195738563426010081374569 3146803922569507561030927)
            ·
              refine ⟨4720205883854261341546391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146803922569507561030927 4720205883854261341546391)
              ·
                refine ⟨7080308825781392012319587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720205883854261341546391 7080308825781392012319587)
                ·
                  refine ⟨10620463238672088018479381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7080308825781392012319587 10620463238672088018479381)
                  ·
                    refine ⟨497834214312754125866221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10620463238672088018479381 497834214312754125866221)
                    ·
                      rfl

theorem cell23_2908586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2908586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908586 prefixEnd_2908586 := by exact prefixLift 2908586
  have htrace : WordTrace (prefixWord ++ tailWord_2908586) baseStart_2908586 baseEnd_2908586 := by
    simpa [prefixWord, tailWord_2908586, baseEnd_2908586] using wordTrace_append hprefix tailTrace_2908586
  have hstable : (prefixWord ++ tailWord_2908586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908586).length < 2 ^ (prefixWord ++ tailWord_2908586).sum := by decide
  have hdescent : baseEnd_2908586 < baseStart_2908586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908589 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2908589 : Nat := 118140960795 + 2908589 * 2 ^ 59
def prefixEnd_2908589 : Nat := 4983230072969 + 3 ^ 40 * 2908589 * 2
def baseEnd_2908589 : Nat := 1493504183380225865861149

theorem tailTrace_2908589 : CollatzResearch.WordTrace tailWord_2908589 prefixEnd_2908589 1493504183380225865861149 := by
  unfold tailWord_2908589
  simp only [CollatzResearch.WordTrace]
  refine ⟨106084956059686275298224821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70723304039790850198816547 106084956059686275298224821)
  ·
    refine ⟨9945464630595588309208577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106084956059686275298224821 9945464630595588309208577)
    ·
      refine ⟨7459098472946691231906433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9945464630595588309208577 7459098472946691231906433)
      ·
        refine ⟨5594323854710018423929825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7459098472946691231906433 5594323854710018423929825)
        ·
          refine ⟨4195742891032513817947369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5594323854710018423929825 4195742891032513817947369)
          ·
            refine ⟨3146807168274385363460527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195742891032513817947369 3146807168274385363460527)
            ·
              refine ⟨4720210752411578045190791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146807168274385363460527 4720210752411578045190791)
              ·
                refine ⟨7080316128617367067786187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720210752411578045190791 7080316128617367067786187)
                ·
                  refine ⟨10620474192926050601679281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7080316128617367067786187 10620474192926050601679281)
                  ·
                    refine ⟨7965355644694537951259461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10620474192926050601679281 7965355644694537951259461)
                    ·
                      refine ⟨1493504183380225865861149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7965355644694537951259461 1493504183380225865861149)
                      ·
                        rfl

theorem cell23_2908589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2908589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908589 prefixEnd_2908589 := by exact prefixLift 2908589
  have htrace : WordTrace (prefixWord ++ tailWord_2908589) baseStart_2908589 baseEnd_2908589 := by
    simpa [prefixWord, tailWord_2908589, baseEnd_2908589] using wordTrace_append hprefix tailTrace_2908589
  have hstable : (prefixWord ++ tailWord_2908589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908589).length < 2 ^ (prefixWord ++ tailWord_2908589).sum := by decide
  have hdescent : baseEnd_2908589 < baseStart_2908589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908643 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2908643 : Nat := 118140960795 + 2908643 * 2 ^ 59
def prefixEnd_2908643 : Nat := 4983230072969 + 3 ^ 40 * 2908643 * 2
def baseEnd_2908643 : Nat := 1493531911335568654585901

theorem tailTrace_2908643 : CollatzResearch.WordTrace tailWord_2908643 prefixEnd_2908643 1493531911335568654585901 := by
  unfold tailWord_2908643
  simp only [CollatzResearch.WordTrace]
  refine ⟨106086925601490642520690583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70724617067660428347127055 106086925601490642520690583)
  ·
    refine ⟨159130388402235963781035875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106086925601490642520690583 159130388402235963781035875)
    ·
      refine ⟨238695582603353945671553813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159130388402235963781035875 238695582603353945671553813)
      ·
        refine ⟨11188855434532216203354085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238695582603353945671553813 11188855434532216203354085)
        ·
          refine ⟨2097910393974790538128891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11188855434532216203354085 2097910393974790538128891)
          ·
            refine ⟨3146865590962185807193337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097910393974790538128891 3146865590962185807193337)
            ·
              refine ⟨2360149193221639355395003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146865590962185807193337 2360149193221639355395003)
              ·
                refine ⟨3540223789832459033092505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360149193221639355395003 3540223789832459033092505)
                ·
                  refine ⟨2655167842374344274819379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540223789832459033092505 2655167842374344274819379)
                  ·
                    refine ⟨3982751763561516412229069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655167842374344274819379 3982751763561516412229069)
                    ·
                      refine ⟨1493531911335568654585901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3982751763561516412229069 1493531911335568654585901)
                      ·
                        rfl

theorem cell23_2908643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2908643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908643 prefixEnd_2908643 := by exact prefixLift 2908643
  have htrace : WordTrace (prefixWord ++ tailWord_2908643) baseStart_2908643 baseEnd_2908643 := by
    simpa [prefixWord, tailWord_2908643, baseEnd_2908643] using wordTrace_append hprefix tailTrace_2908643
  have hstable : (prefixWord ++ tailWord_2908643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908643).length < 2 ^ (prefixWord ++ tailWord_2908643).sum := by decide
  have hdescent : baseEnd_2908643 < baseStart_2908643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908705 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2908705 : Nat := 118140960795 + 2908705 * 2 ^ 59
def prefixEnd_2908705 : Nat := 4983230072969 + 3 ^ 40 * 2908705 * 2
def baseEnd_2908705 : Nat := 1493563747136147412010615

theorem tailTrace_2908705 : CollatzResearch.WordTrace tailWord_2908705 prefixEnd_2908705 1493563747136147412010615 := by
  unfold tailWord_2908705
  simp only [CollatzResearch.WordTrace]
  refine ⟨106089186927266027109447569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70726124618177351406298379 106089186927266027109447569)
  ·
    refine ⟨79566890195449520332085677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106089186927266027109447569 79566890195449520332085677)
    ·
      refine ⟨29837583823293570124532129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79566890195449520332085677 29837583823293570124532129)
      ·
        refine ⟨22378187867470177593399097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29837583823293570124532129 22378187867470177593399097)
        ·
          refine ⟨16783640900602633195049323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22378187867470177593399097 16783640900602633195049323)
          ·
            refine ⟨25175461350903949792573985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783640900602633195049323 25175461350903949792573985)
            ·
              refine ⟨18881596013177962344430489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25175461350903949792573985 18881596013177962344430489)
              ·
                refine ⟨14161197009883471758322867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18881596013177962344430489 14161197009883471758322867)
                ·
                  refine ⟨21241795514825207637484301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14161197009883471758322867 21241795514825207637484301)
                  ·
                    refine ⟨7965673318059452864056613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21241795514825207637484301 7965673318059452864056613)
                    ·
                      refine ⟨1493563747136147412010615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7965673318059452864056613 1493563747136147412010615)
                      ·
                        rfl

theorem cell23_2908705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2908705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908705 prefixEnd_2908705 := by exact prefixLift 2908705
  have htrace : WordTrace (prefixWord ++ tailWord_2908705) baseStart_2908705 baseEnd_2908705 := by
    simpa [prefixWord, tailWord_2908705, baseEnd_2908705] using wordTrace_append hprefix tailTrace_2908705
  have hstable : (prefixWord ++ tailWord_2908705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908705).length < 2 ^ (prefixWord ++ tailWord_2908705).sum := by decide
  have hdescent : baseEnd_2908705 < baseStart_2908705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908722 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_2908722 : Nat := 118140960795 + 2908722 * 2 ^ 59
def prefixEnd_2908722 : Nat := 4983230072969 + 3 ^ 40 * 2908722 * 2
def baseEnd_2908722 : Nat := 1493572476307273845498037

theorem tailTrace_2908722 : CollatzResearch.WordTrace tailWord_2908722 prefixEnd_2908722 1493572476307273845498037 := by
  unfold tailWord_2908722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522451742051109753204105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70726537978802959341877613 26522451742051109753204105)
  ·
    refine ⟨19891838806538332314903079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26522451742051109753204105 19891838806538332314903079)
    ·
      refine ⟨29837758209807498472354619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19891838806538332314903079 29837758209807498472354619)
      ·
        refine ⟨44756637314711247708531929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29837758209807498472354619 44756637314711247708531929)
        ·
          refine ⟨33567477986033435781398947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44756637314711247708531929 33567477986033435781398947)
          ·
            refine ⟨50351216979050153672098421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33567477986033435781398947 50351216979050153672098421)
            ·
              refine ⟨4720426591785951906759227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50351216979050153672098421 4720426591785951906759227)
              ·
                refine ⟨7080639887678927860138841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720426591785951906759227 7080639887678927860138841)
                ·
                  refine ⟨5310479915759195895104131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7080639887678927860138841 5310479915759195895104131)
                  ·
                    refine ⟨7965719873638793842656197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310479915759195895104131 7965719873638793842656197)
                    ·
                      refine ⟨1493572476307273845498037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7965719873638793842656197 1493572476307273845498037)
                      ·
                        rfl

theorem cell23_2908722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_2908722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908722 prefixEnd_2908722 := by exact prefixLift 2908722
  have htrace : WordTrace (prefixWord ++ tailWord_2908722) baseStart_2908722 baseEnd_2908722 := by
    simpa [prefixWord, tailWord_2908722, baseEnd_2908722] using wordTrace_append hprefix tailTrace_2908722
  have hstable : (prefixWord ++ tailWord_2908722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908722).length < 2 ^ (prefixWord ++ tailWord_2908722).sum := by decide
  have hdescent : baseEnd_2908722 < baseStart_2908722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908749 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2908749 : Nat := 118140960795 + 2908749 * 2 ^ 59
def prefixEnd_2908749 : Nat := 4983230072969 + 3 ^ 40 * 2908749 * 2
def baseEnd_2908749 : Nat := 497862113428315079953471

theorem tailTrace_2908749 : CollatzResearch.WordTrace tailWord_2908749 prefixEnd_2908749 497862113428315079953471 := by
  unfold tailWord_2908749
  simp only [CollatzResearch.WordTrace]
  refine ⟨106090791739106622624049301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70727194492737748416032867 106090791739106622624049301)
  ·
    refine ⟨4973005862770622935502311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106090791739106622624049301 4973005862770622935502311)
    ·
      refine ⟨7459508794155934403253467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973005862770622935502311 7459508794155934403253467)
      ·
        refine ⟨11189263191233901604880201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459508794155934403253467 11189263191233901604880201)
        ·
          refine ⟨8391947393425426203660151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11189263191233901604880201 8391947393425426203660151)
          ·
            refine ⟨12587921090138139305490227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391947393425426203660151 12587921090138139305490227)
            ·
              refine ⟨18881881635207208958235341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12587921090138139305490227 18881881635207208958235341)
              ·
                refine ⟨7080705613202703359338253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18881881635207208958235341 7080705613202703359338253)
                ·
                  refine ⟨2655264604951013759751845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7080705613202703359338253 2655264604951013759751845)
                  ·
                    refine ⟨497862113428315079953471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655264604951013759751845 497862113428315079953471)
                    ·
                      rfl

theorem cell23_2908749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2908749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908749 prefixEnd_2908749 := by exact prefixLift 2908749
  have htrace : WordTrace (prefixWord ++ tailWord_2908749) baseStart_2908749 baseEnd_2908749 := by
    simpa [prefixWord, tailWord_2908749, baseEnd_2908749] using wordTrace_append hprefix tailTrace_2908749
  have hstable : (prefixWord ++ tailWord_2908749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908749).length < 2 ^ (prefixWord ++ tailWord_2908749).sum := by decide
  have hdescent : baseEnd_2908749 < baseStart_2908749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908812 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_2908812 : Nat := 118140960795 + 2908812 * 2 ^ 59
def prefixEnd_2908812 : Nat := 4983230072969 + 3 ^ 40 * 2908812 * 2
def baseEnd_2908812 : Nat := 1493618689566178493372623

theorem tailTrace_2908812 : CollatzResearch.WordTrace tailWord_2908812 prefixEnd_2908812 1493618689566178493372623 := by
  unfold tailWord_2908812
  simp only [CollatzResearch.WordTrace]
  refine ⟨53046544768939192191796345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70728726358585589589061793 53046544768939192191796345)
  ·
    refine ⟨39784908576704394143847259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53046544768939192191796345 39784908576704394143847259)
    ·
      refine ⟨59677362865056591215770889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39784908576704394143847259 59677362865056591215770889)
      ·
        refine ⟨44758022148792443411828167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59677362865056591215770889 44758022148792443411828167)
        ·
          refine ⟨67137033223188665117742251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44758022148792443411828167 67137033223188665117742251)
          ·
            refine ⟨100705549834782997676613377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67137033223188665117742251 100705549834782997676613377)
            ·
              refine ⟨75529162376087248257460033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100705549834782997676613377 75529162376087248257460033)
              ·
                refine ⟨56646871782065436193095025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75529162376087248257460033 56646871782065436193095025)
                ·
                  refine ⟨42485153836549077144821269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56646871782065436193095025 42485153836549077144821269)
                  ·
                    refine ⟨1991491586088237991163497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42485153836549077144821269 1991491586088237991163497)
                    ·
                      refine ⟨1493618689566178493372623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991491586088237991163497 1493618689566178493372623)
                      ·
                        rfl

theorem cell23_2908812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_2908812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908812 prefixEnd_2908812 := by exact prefixLift 2908812
  have htrace : WordTrace (prefixWord ++ tailWord_2908812) baseStart_2908812 baseEnd_2908812 := by
    simpa [prefixWord, tailWord_2908812, baseEnd_2908812] using wordTrace_append hprefix tailTrace_2908812
  have hstable : (prefixWord ++ tailWord_2908812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908812).length < 2 ^ (prefixWord ++ tailWord_2908812).sum := by decide
  have hdescent : baseEnd_2908812 < baseStart_2908812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908825 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2908825 : Nat := 118140960795 + 2908825 * 2 ^ 59
def prefixEnd_2908825 : Nat := 4983230072969 + 3 ^ 40 * 2908825 * 2
def baseEnd_2908825 : Nat := 1493625364814686942510063

theorem tailTrace_2908825 : CollatzResearch.WordTrace tailWord_2908825 prefixEnd_2908825 1493625364814686942510063 := by
  unfold tailWord_2908825
  simp only [CollatzResearch.WordTrace]
  refine ⟨106093563686831287603815929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70729042457887525069210619 106093563686831287603815929)
  ·
    refine ⟨79570172765123465702861947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106093563686831287603815929 79570172765123465702861947)
    ·
      refine ⟨119355259147685198554292921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79570172765123465702861947 119355259147685198554292921)
      ·
        refine ⟨89516444360763898915719691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119355259147685198554292921 89516444360763898915719691)
        ·
          refine ⟨134274666541145848373579537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89516444360763898915719691 134274666541145848373579537)
          ·
            refine ⟨100705999905859386280184653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134274666541145848373579537 100705999905859386280184653)
            ·
              refine ⟨37764749964697269855069245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100705999905859386280184653 37764749964697269855069245)
              ·
                refine ⟨14161781236761476195650967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37764749964697269855069245 14161781236761476195650967)
                ·
                  refine ⟨21242671855142214293476451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14161781236761476195650967 21242671855142214293476451)
                  ·
                    refine ⟨31864007782713321440214677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21242671855142214293476451 31864007782713321440214677)
                    ·
                      refine ⟨1493625364814686942510063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31864007782713321440214677 1493625364814686942510063)
                      ·
                        rfl

theorem cell23_2908825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2908825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908825 prefixEnd_2908825 := by exact prefixLift 2908825
  have htrace : WordTrace (prefixWord ++ tailWord_2908825) baseStart_2908825 baseEnd_2908825 := by
    simpa [prefixWord, tailWord_2908825, baseEnd_2908825] using wordTrace_append hprefix tailTrace_2908825
  have hstable : (prefixWord ++ tailWord_2908825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908825).length < 2 ^ (prefixWord ++ tailWord_2908825).sum := by decide
  have hdescent : baseEnd_2908825 < baseStart_2908825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908829 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2908829 : Nat := 118140960795 + 2908829 * 2 ^ 59
def prefixEnd_2908829 : Nat := 4983230072969 + 3 ^ 40 * 2908829 * 2
def baseEnd_2908829 : Nat := 1493627418737304926860045

theorem tailTrace_2908829 : CollatzResearch.WordTrace tailWord_2908829 prefixEnd_2908829 1493627418737304926860045 := by
  unfold tailWord_2908829
  simp only [CollatzResearch.WordTrace]
  refine ⟨106093709578816796286961541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70729139719211197524641027 106093709578816796286961541)
  ·
    refine ⟨19892570546028149303805289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106093709578816796286961541 19892570546028149303805289)
    ·
      refine ⟨14919427909521111977853967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19892570546028149303805289 14919427909521111977853967)
      ·
        refine ⟨22379141864281667966780951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14919427909521111977853967 22379141864281667966780951)
        ·
          refine ⟨33568712796422501950171427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22379141864281667966780951 33568712796422501950171427)
          ·
            refine ⟨50353069194633752925257141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33568712796422501950171427 50353069194633752925257141)
            ·
              refine ⟨4720600236996914336742857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50353069194633752925257141 4720600236996914336742857)
              ·
                refine ⟨3540450177747685752557143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4720600236996914336742857 3540450177747685752557143)
                ·
                  refine ⟨5310675266621528628835715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540450177747685752557143 5310675266621528628835715)
                  ·
                    refine ⟨7966012899932292943253573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5310675266621528628835715 7966012899932292943253573)
                    ·
                      refine ⟨1493627418737304926860045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7966012899932292943253573 1493627418737304926860045)
                      ·
                        rfl

theorem cell23_2908829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2908829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908829 prefixEnd_2908829 := by exact prefixLift 2908829
  have htrace : WordTrace (prefixWord ++ tailWord_2908829) baseStart_2908829 baseEnd_2908829 := by
    simpa [prefixWord, tailWord_2908829, baseEnd_2908829] using wordTrace_append hprefix tailTrace_2908829
  have hstable : (prefixWord ++ tailWord_2908829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908829).length < 2 ^ (prefixWord ++ tailWord_2908829).sum := by decide
  have hdescent : baseEnd_2908829 < baseStart_2908829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908863 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 1, 2, 2]
def baseStart_2908863 : Nat := 118140960795 + 2908863 * 2 ^ 59
def prefixEnd_2908863 : Nat := 4983230072969 + 3 ^ 40 * 2908863 * 2
def baseEnd_2908863 : Nat := 1493644877079557793834889

theorem tailTrace_2908863 : CollatzResearch.WordTrace tailWord_2908863 prefixEnd_2908863 1493644877079557793834889 := by
  unfold tailWord_2908863
  simp only [CollatzResearch.WordTrace]
  refine ⟨106094949660693620093699243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70729966440462413395799495 106094949660693620093699243)
  ·
    refine ⟨159142424491040430140548865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106094949660693620093699243 159142424491040430140548865)
    ·
      refine ⟨119356818368280322605411649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159142424491040430140548865 119356818368280322605411649)
      ·
        refine ⟨89517613776210241954058737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119356818368280322605411649 89517613776210241954058737)
        ·
          refine ⟨67138210332157681465544053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89517613776210241954058737 67138210332157681465544053)
          ·
            refine ⟨6294207218639782637394755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67138210332157681465544053 6294207218639782637394755)
            ·
              refine ⟨9441310827959673956092133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294207218639782637394755 9441310827959673956092133)
              ·
                refine ⟨1770245780242438866767275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9441310827959673956092133 1770245780242438866767275)
                ·
                  refine ⟨2655368670363658300150913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770245780242438866767275 2655368670363658300150913)
                  ·
                    refine ⟨1991526502772743725113185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2655368670363658300150913 1991526502772743725113185)
                    ·
                      refine ⟨1493644877079557793834889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991526502772743725113185 1493644877079557793834889)
                      ·
                        rfl

theorem cell23_2908863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_2908863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908863 prefixEnd_2908863 := by exact prefixLift 2908863
  have htrace : WordTrace (prefixWord ++ tailWord_2908863) baseStart_2908863 baseEnd_2908863 := by
    simpa [prefixWord, tailWord_2908863, baseEnd_2908863] using wordTrace_append hprefix tailTrace_2908863
  have hstable : (prefixWord ++ tailWord_2908863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908863).length < 2 ^ (prefixWord ++ tailWord_2908863).sum := by decide
  have hdescent : baseEnd_2908863 < baseStart_2908863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908875 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_2908875 : Nat := 118140960795 + 2908875 * 2 ^ 59
def prefixEnd_2908875 : Nat := 4983230072969 + 3 ^ 40 * 2908875 * 2
def baseEnd_2908875 : Nat := 1493651038847411746884833

theorem tailTrace_2908875 : CollatzResearch.WordTrace tailWord_2908875 prefixEnd_2908875 1493651038847411746884833 := by
  unfold tailWord_2908875
  simp only [CollatzResearch.WordTrace]
  refine ⟨106095387336650146143136079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70730258224433430762090719 106095387336650146143136079)
  ·
    refine ⟨159143081004975219214704119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106095387336650146143136079 159143081004975219214704119)
    ·
      refine ⟨238714621507462828822056179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159143081004975219214704119 238714621507462828822056179)
      ·
        refine ⟨358071932261194243233084269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238714621507462828822056179 358071932261194243233084269)
        ·
          refine ⟨134276974597947841212406601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358071932261194243233084269 134276974597947841212406601)
          ·
            refine ⟨100707730948460880909304951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134276974597947841212406601 100707730948460880909304951)
            ·
              refine ⟨151061596422691321363957427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100707730948460880909304951 151061596422691321363957427)
              ·
                refine ⟨226592394634036982045936141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151061596422691321363957427 226592394634036982045936141)
                ·
                  refine ⟨84972147987763868267226053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226592394634036982045936141 84972147987763868267226053)
                  ·
                    refine ⟨15932277747705725300104885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84972147987763868267226053 15932277747705725300104885)
                    ·
                      refine ⟨1493651038847411746884833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15932277747705725300104885 1493651038847411746884833)
                      ·
                        rfl

theorem cell23_2908875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_2908875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908875 prefixEnd_2908875 := by exact prefixLift 2908875
  have htrace : WordTrace (prefixWord ++ tailWord_2908875) baseStart_2908875 baseEnd_2908875 := by
    simpa [prefixWord, tailWord_2908875, baseEnd_2908875] using wordTrace_append hprefix tailTrace_2908875
  have hstable : (prefixWord ++ tailWord_2908875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908875).length < 2 ^ (prefixWord ++ tailWord_2908875).sum := by decide
  have hdescent : baseEnd_2908875 < baseStart_2908875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908889 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 3, 3, 2]
def baseStart_2908889 : Nat := 118140960795 + 2908889 * 2 ^ 59
def prefixEnd_2908889 : Nat := 4983230072969 + 3 ^ 40 * 2908889 * 2
def baseEnd_2908889 : Nat := 1493658227576574692109769

theorem tailTrace_2908889 : CollatzResearch.WordTrace tailWord_2908889 prefixEnd_2908889 1493658227576574692109769 := by
  unfold tailWord_2908889
  simp only [CollatzResearch.WordTrace]
  refine ⟨106095897958599426534145721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70730598639066284356097147 106095897958599426534145721)
  ·
    refine ⟨79571923468949569900609291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106095897958599426534145721 79571923468949569900609291)
    ·
      refine ⟨119357885203424354850913937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79571923468949569900609291 119357885203424354850913937)
      ·
        refine ⟨89518413902568266138185453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119357885203424354850913937 89518413902568266138185453)
        ·
          refine ⟨33569405213463099801819545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89518413902568266138185453 33569405213463099801819545)
          ·
            refine ⟨25177053910097324851364659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33569405213463099801819545 25177053910097324851364659)
            ·
              refine ⟨37765580865145987277046989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25177053910097324851364659 37765580865145987277046989)
              ·
                refine ⟨14162092824429745228892621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37765580865145987277046989 14162092824429745228892621)
                ·
                  refine ⟨5310784809161154460834733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14162092824429745228892621 5310784809161154460834733)
                  ·
                    refine ⟨1991544303435432922813025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5310784809161154460834733 1991544303435432922813025)
                    ·
                      refine ⟨1493658227576574692109769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991544303435432922813025 1493658227576574692109769)
                      ·
                        rfl

theorem cell23_2908889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_2908889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908889 prefixEnd_2908889 := by exact prefixLift 2908889
  have htrace : WordTrace (prefixWord ++ tailWord_2908889) baseStart_2908889 baseEnd_2908889 := by
    simpa [prefixWord, tailWord_2908889, baseEnd_2908889] using wordTrace_append hprefix tailTrace_2908889
  have hstable : (prefixWord ++ tailWord_2908889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908889).length < 2 ^ (prefixWord ++ tailWord_2908889).sum := by decide
  have hdescent : baseEnd_2908889 < baseStart_2908889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908922 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_2908922 : Nat := 118140960795 + 2908922 * 2 ^ 59
def prefixEnd_2908922 : Nat := 4983230072969 + 3 ^ 40 * 2908922 * 2
def baseEnd_2908922 : Nat := 1493675172438173062997117

theorem tailTrace_2908922 : CollatzResearch.WordTrace tailWord_2908922 prefixEnd_2908922 1493675172438173062997117 := by
  unfold tailWord_2908922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524275391869968292524255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70731401044986582113398013 26524275391869968292524255)
  ·
    refine ⟨39786413087804952438786383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26524275391869968292524255 39786413087804952438786383)
    ·
      refine ⟨59679619631707428658179575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39786413087804952438786383 59679619631707428658179575)
      ·
        refine ⟨89519429447561142987269363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59679619631707428658179575 89519429447561142987269363)
        ·
          refine ⟨134279144171341714480904045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89519429447561142987269363 134279144171341714480904045)
          ·
            refine ⟨50354679064253142930339017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134279144171341714480904045 50354679064253142930339017)
            ·
              refine ⟨37766009298189857197754263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50354679064253142930339017 37766009298189857197754263)
              ·
                refine ⟨56649013947284785796631395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37766009298189857197754263 56649013947284785796631395)
                ·
                  refine ⟨84973520920927178694947093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56649013947284785796631395 84973520920927178694947093)
                  ·
                    refine ⟨3983133793168461501325645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84973520920927178694947093 3983133793168461501325645)
                    ·
                      refine ⟨1493675172438173062997117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983133793168461501325645 1493675172438173062997117)
                      ·
                        rfl

theorem cell23_2908922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_2908922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908922 prefixEnd_2908922 := by exact prefixLift 2908922
  have htrace : WordTrace (prefixWord ++ tailWord_2908922) baseStart_2908922 baseEnd_2908922 := by
    simpa [prefixWord, tailWord_2908922, baseEnd_2908922] using wordTrace_append hprefix tailTrace_2908922
  have hstable : (prefixWord ++ tailWord_2908922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908922).length < 2 ^ (prefixWord ++ tailWord_2908922).sum := by decide
  have hdescent : baseEnd_2908922 < baseStart_2908922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908930 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_2908930 : Nat := 118140960795 + 2908930 * 2 ^ 59
def prefixEnd_2908930 : Nat := 4983230072969 + 3 ^ 40 * 2908930 * 2
def baseEnd_2908930 : Nat := 1493679280283409031697081

theorem tailTrace_2908930 : CollatzResearch.WordTrace tailWord_2908930 prefixEnd_2908930 1493679280283409031697081 := by
  unfold tailWord_2908930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524348337862722634097061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70731595567633927024258829 26524348337862722634097061)
  ·
    refine ⟨4973315313349260493893199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26524348337862722634097061 4973315313349260493893199)
    ·
      refine ⟨7459972970023890740839799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973315313349260493893199 7459972970023890740839799)
      ·
        refine ⟨11189959455035836111259699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459972970023890740839799 11189959455035836111259699)
        ·
          refine ⟨16784939182553754166889549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189959455035836111259699 16784939182553754166889549)
          ·
            refine ⟨6294352193457657812583581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16784939182553754166889549 6294352193457657812583581)
            ·
              refine ⟨2360382072546621679718843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6294352193457657812583581 2360382072546621679718843)
              ·
                refine ⟨3540573108819932519578265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360382072546621679718843 3540573108819932519578265)
                ·
                  refine ⟨2655429831614949389683699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540573108819932519578265 2655429831614949389683699)
                  ·
                    refine ⟨3983144747422424084525549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655429831614949389683699 3983144747422424084525549)
                    ·
                      refine ⟨1493679280283409031697081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983144747422424084525549 1493679280283409031697081)
                      ·
                        rfl

theorem cell23_2908930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_2908930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908930 prefixEnd_2908930 := by exact prefixLift 2908930
  have htrace : WordTrace (prefixWord ++ tailWord_2908930) baseStart_2908930 baseEnd_2908930 := by
    simpa [prefixWord, tailWord_2908930, baseEnd_2908930] using wordTrace_append hprefix tailTrace_2908930
  have hstable : (prefixWord ++ tailWord_2908930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908930).length < 2 ^ (prefixWord ++ tailWord_2908930).sum := by decide
  have hdescent : baseEnd_2908930 < baseStart_2908930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908936 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_2908936 : Nat := 118140960795 + 2908936 * 2 ^ 59
def prefixEnd_2908936 : Nat := 4983230072969 + 3 ^ 40 * 2908936 * 2
def baseEnd_2908936 : Nat := 1493682361167336008222053

theorem tailTrace_2908936 : CollatzResearch.WordTrace tailWord_2908936 prefixEnd_2908936 1493682361167336008222053 := by
  unfold tailWord_2908936
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048806094714576780553331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70731741459619435707404441 53048806094714576780553331)
  ·
    refine ⟨79573209142071865170829997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53048806094714576780553331 79573209142071865170829997)
    ·
      refine ⟨29839953428276949439061249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79573209142071865170829997 29839953428276949439061249)
      ·
        refine ⟨22379965071207712079295937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29839953428276949439061249 22379965071207712079295937)
        ·
          refine ⟨16784973803405784059471953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22379965071207712079295937 16784973803405784059471953)
          ·
            refine ⟨12588730352554338044603965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16784973803405784059471953 12588730352554338044603965)
            ·
              refine ⟨4720773882207876766726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12588730352554338044603965 4720773882207876766726487)
              ·
                refine ⟨7081160823311815150089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720773882207876766726487 7081160823311815150089731)
                ·
                  refine ⟨10621741234967722725134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081160823311815150089731 10621741234967722725134597)
                  ·
                    refine ⟨1991576481556448010962737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10621741234967722725134597 1991576481556448010962737)
                    ·
                      refine ⟨1493682361167336008222053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991576481556448010962737 1493682361167336008222053)
                      ·
                        rfl

theorem cell23_2908936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_2908936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908936 prefixEnd_2908936 := by exact prefixLift 2908936
  have htrace : WordTrace (prefixWord ++ tailWord_2908936) baseStart_2908936 baseEnd_2908936 := by
    simpa [prefixWord, tailWord_2908936, baseEnd_2908936] using wordTrace_append hprefix tailTrace_2908936
  have hstable : (prefixWord ++ tailWord_2908936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908936).length < 2 ^ (prefixWord ++ tailWord_2908936).sum := by decide
  have hdescent : baseEnd_2908936 < baseStart_2908936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908992 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2908992 : Nat := 118140960795 + 2908992 * 2 ^ 59
def prefixEnd_2908992 : Nat := 4983230072969 + 3 ^ 40 * 2908992 * 2
def baseEnd_2908992 : Nat := 1493711116083987789121795

theorem tailTrace_2908992 : CollatzResearch.WordTrace tailWord_2908992 prefixEnd_2908992 1493711116083987789121795 := by
  unfold tailWord_2908992
  simp only [CollatzResearch.WordTrace]
  refine ⟨53049827338613137562572615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70733103118150850083430153 53049827338613137562572615)
  ·
    refine ⟨79574741007919706343858923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53049827338613137562572615 79574741007919706343858923)
    ·
      refine ⟨119362111511879559515788385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79574741007919706343858923 119362111511879559515788385)
      ·
        refine ⟨89521583633909669636841289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119362111511879559515788385 89521583633909669636841289)
        ·
          refine ⟨67141187725432252227630967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89521583633909669636841289 67141187725432252227630967)
          ·
            refine ⟨100711781588148378341446451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67141187725432252227630967 100711781588148378341446451)
            ·
              refine ⟨151067672382222567512169677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100711781588148378341446451 151067672382222567512169677)
              ·
                refine ⟨56650377143333462817063629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151067672382222567512169677 56650377143333462817063629)
                ·
                  refine ⟨21243891428750048556398861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56650377143333462817063629 21243891428750048556398861)
                  ·
                    refine ⟨7966459285781268208649573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21243891428750048556398861 7966459285781268208649573)
                    ·
                      refine ⟨1493711116083987789121795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7966459285781268208649573 1493711116083987789121795)
                      ·
                        rfl

theorem cell23_2908992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2908992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2908992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2908992 prefixEnd_2908992 := by exact prefixLift 2908992
  have htrace : WordTrace (prefixWord ++ tailWord_2908992) baseStart_2908992 baseEnd_2908992 := by
    simpa [prefixWord, tailWord_2908992, baseEnd_2908992] using wordTrace_append hprefix tailTrace_2908992
  have hstable : (prefixWord ++ tailWord_2908992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908992).length < 2 ^ (prefixWord ++ tailWord_2908992).sum := by decide
  have hdescent : baseEnd_2908992 < baseStart_2908992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909049 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 6]
def baseStart_2909049 : Nat := 118140960795 + 2909049 * 2 ^ 59
def prefixEnd_2909049 : Nat := 4983230072969 + 3 ^ 40 * 2909049 * 2
def baseEnd_2909049 : Nat := 165971153831254896234337

theorem tailTrace_2909049 : CollatzResearch.WordTrace tailWord_2909049 prefixEnd_2909049 165971153831254896234337 := by
  unfold tailWord_2909049
  simp only [CollatzResearch.WordTrace]
  refine ⟨106101733638019773859970201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70734489092013182573313467 106101733638019773859970201)
  ·
    refine ⟨79576300228514830394977651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106101733638019773859970201 79576300228514830394977651)
    ·
      refine ⟨119364450342772245592466477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79576300228514830394977651 119364450342772245592466477)
      ·
        refine ⟨44761668878539592097174929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119364450342772245592466477 44761668878539592097174929)
        ·
          refine ⟨33571251658904694072881197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44761668878539592097174929 33571251658904694072881197)
          ·
            refine ⟨12589219372089260277330449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33571251658904694072881197 12589219372089260277330449)
            ·
              refine ⟨9441914529066945207997837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12589219372089260277330449 9441914529066945207997837)
              ·
                refine ⟨3540717948400104452999189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9441914529066945207997837 3540717948400104452999189)
                ·
                  refine ⟨165971153831254896234337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3540717948400104452999189 165971153831254896234337)
                  ·
                    rfl

theorem cell23_2909049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_2909049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909049 prefixEnd_2909049 := by exact prefixLift 2909049
  have htrace : WordTrace (prefixWord ++ tailWord_2909049) baseStart_2909049 baseEnd_2909049 := by
    simpa [prefixWord, tailWord_2909049, baseEnd_2909049] using wordTrace_append hprefix tailTrace_2909049
  have hstable : (prefixWord ++ tailWord_2909049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909049).length < 2 ^ (prefixWord ++ tailWord_2909049).sum := by decide
  have hdescent : baseEnd_2909049 < baseStart_2909049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909063 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2909063 : Nat := 118140960795 + 2909063 * 2 ^ 59
def prefixEnd_2909063 : Nat := 4983230072969 + 3 ^ 40 * 2909063 * 2
def baseEnd_2909063 : Nat := 1493747573210457011333969

theorem tailTrace_2909063 : CollatzResearch.WordTrace tailWord_2909063 prefixEnd_2909063 1493747573210457011333969 := by
  unfold tailWord_2909063
  simp only [CollatzResearch.WordTrace]
  refine ⟨106102244259969054250979843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70734829506646036167319895 106102244259969054250979843)
  ·
    refine ⟨159153366389953581376469765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106102244259969054250979843 159153366389953581376469765)
    ·
      refine ⟨29841256198116296508088081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159153366389953581376469765 29841256198116296508088081)
      ·
        refine ⟨22380942148587222381066061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29841256198116296508088081 22380942148587222381066061)
        ·
          refine ⟨8392853305720208392899773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22380942148587222381066061 8392853305720208392899773)
          ·
            refine ⟨3147319989645078147337415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8392853305720208392899773 3147319989645078147337415)
            ·
              refine ⟨4720979984467617221006123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147319989645078147337415 4720979984467617221006123)
              ·
                refine ⟨7081469976701425831509185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720979984467617221006123 7081469976701425831509185)
                ·
                  refine ⟨5311102482526069373631889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081469976701425831509185 5311102482526069373631889)
                  ·
                    refine ⟨3983326861894552030223917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311102482526069373631889 3983326861894552030223917)
                    ·
                      refine ⟨1493747573210457011333969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983326861894552030223917 1493747573210457011333969)
                      ·
                        rfl

theorem cell23_2909063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2909063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909063 prefixEnd_2909063 := by exact prefixLift 2909063
  have htrace : WordTrace (prefixWord ++ tailWord_2909063) baseStart_2909063 baseEnd_2909063 := by
    simpa [prefixWord, tailWord_2909063, baseEnd_2909063] using wordTrace_append hprefix tailTrace_2909063
  have hstable : (prefixWord ++ tailWord_2909063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909063).length < 2 ^ (prefixWord ++ tailWord_2909063).sum := by decide
  have hdescent : baseEnd_2909063 < baseStart_2909063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909072 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_2909072 : Nat := 118140960795 + 2909072 * 2 ^ 59
def prefixEnd_2909072 : Nat := 4983230072969 + 3 ^ 40 * 2909072 * 2
def baseEnd_2909072 : Nat := 1493752194536347476121427

theorem tailTrace_2909072 : CollatzResearch.WordTrace tailWord_2909072 prefixEnd_2909072 1493752194536347476121427 := by
  unfold tailWord_2909072
  simp only [CollatzResearch.WordTrace]
  refine ⟨53051286258468224394028735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70735048344624299192038313 53051286258468224394028735)
  ·
    refine ⟨79576929387702336591043103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53051286258468224394028735 79576929387702336591043103)
    ·
      refine ⟨119365394081553504886564655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79576929387702336591043103 119365394081553504886564655)
      ·
        refine ⟨179048091122330257329846983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119365394081553504886564655 179048091122330257329846983)
        ·
          refine ⟨268572136683495385994770475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179048091122330257329846983 268572136683495385994770475)
          ·
            refine ⟨402858205025243078992155713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268572136683495385994770475 402858205025243078992155713)
            ·
              refine ⟨302143653768932309244116785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402858205025243078992155713 302143653768932309244116785)
              ·
                refine ⟨226607740326699231933087589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302143653768932309244116785 226607740326699231933087589)
                ·
                  refine ⟨42488951311256105987453923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226607740326699231933087589 42488951311256105987453923)
                  ·
                    refine ⟨63733426966884158981180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42488951311256105987453923 63733426966884158981180885)
                    ·
                      refine ⟨1493752194536347476121427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63733426966884158981180885 1493752194536347476121427)
                      ·
                        rfl

theorem cell23_2909072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_2909072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909072 prefixEnd_2909072 := by exact prefixLift 2909072
  have htrace : WordTrace (prefixWord ++ tailWord_2909072) baseStart_2909072 baseEnd_2909072 := by
    simpa [prefixWord, tailWord_2909072, baseEnd_2909072] using wordTrace_append hprefix tailTrace_2909072
  have hstable : (prefixWord ++ tailWord_2909072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909072).length < 2 ^ (prefixWord ++ tailWord_2909072).sum := by decide
  have hdescent : baseEnd_2909072 < baseStart_2909072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909170 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2909170 : Nat := 118140960795 + 2909170 * 2 ^ 59
def prefixEnd_2909170 : Nat := 4983230072969 + 3 ^ 40 * 2909170 * 2
def baseEnd_2909170 : Nat := 1493802515640488092695977

theorem tailTrace_2909170 : CollatzResearch.WordTrace tailWord_2909170 prefixEnd_2909170 1493802515640488092695977 := by
  unfold tailWord_2909170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526536717645352881281241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70737431247054274350083309 26526536717645352881281241)
  ·
    refine ⟨19894902538234014660960931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26526536717645352881281241 19894902538234014660960931)
    ·
      refine ⟨29842353807351021991441397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19894902538234014660960931 29842353807351021991441397)
      ·
        refine ⟨2797720669439158311697631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29842353807351021991441397 2797720669439158311697631)
        ·
          refine ⟨4196581004158737467546447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797720669439158311697631 4196581004158737467546447)
          ·
            refine ⟨6294871506238106201319671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196581004158737467546447 6294871506238106201319671)
            ·
              refine ⟨9442307259357159301979507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294871506238106201319671 9442307259357159301979507)
              ·
                refine ⟨14163460889035738952969261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442307259357159301979507 14163460889035738952969261)
                ·
                  refine ⟨5311297833388402107363473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14163460889035738952969261 5311297833388402107363473)
                  ·
                    refine ⟨3983473375041301580522605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5311297833388402107363473 3983473375041301580522605)
                    ·
                      refine ⟨1493802515640488092695977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983473375041301580522605 1493802515640488092695977)
                      ·
                        rfl

theorem cell23_2909170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2909170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909170 prefixEnd_2909170 := by exact prefixLift 2909170
  have htrace : WordTrace (prefixWord ++ tailWord_2909170) baseStart_2909170 baseEnd_2909170 := by
    simpa [prefixWord, tailWord_2909170, baseEnd_2909170] using wordTrace_append hprefix tailTrace_2909170
  have hstable : (prefixWord ++ tailWord_2909170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909170).length < 2 ^ (prefixWord ++ tailWord_2909170).sum := by decide
  have hdescent : baseEnd_2909170 < baseStart_2909170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909193 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 1, 3, 2]
def baseStart_2909193 : Nat := 118140960795 + 2909193 * 2 ^ 59
def prefixEnd_2909193 : Nat := 4983230072969 + 3 ^ 40 * 2909193 * 2
def baseEnd_2909193 : Nat := 1493814325695541502708371

theorem tailTrace_2909193 : CollatzResearch.WordTrace tailWord_2909193 prefixEnd_2909193 1493814325695541502708371 := by
  unfold tailWord_2909193
  simp only [CollatzResearch.WordTrace]
  refine ⟨106106985749498086453212233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70737990499665390968808155 106106985749498086453212233)
  ·
    refine ⟨79580239312123564839909175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106106985749498086453212233 79580239312123564839909175)
    ·
      refine ⟨119370358968185347259863763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79580239312123564839909175 119370358968185347259863763)
      ·
        refine ⟨179055538452278020889795645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119370358968185347259863763 179055538452278020889795645)
        ·
          refine ⟨67145826919604257833673367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179055538452278020889795645 67145826919604257833673367)
          ·
            refine ⟨100718740379406386750510051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67145826919604257833673367 100718740379406386750510051)
            ·
              refine ⟨151078110569109580125765077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100718740379406386750510051 151078110569109580125765077)
              ·
                refine ⟨3540893216463505784197619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151078110569109580125765077 3540893216463505784197619)
                ·
                  refine ⟨5311339824695258676296429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540893216463505784197619 5311339824695258676296429)
                  ·
                    refine ⟨1991752434260722003611161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5311339824695258676296429 1991752434260722003611161)
                    ·
                      refine ⟨1493814325695541502708371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991752434260722003611161 1493814325695541502708371)
                      ·
                        rfl

theorem cell23_2909193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3, 2].length) (baseStart_2909193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909193 prefixEnd_2909193 := by exact prefixLift 2909193
  have htrace : WordTrace (prefixWord ++ tailWord_2909193) baseStart_2909193 baseEnd_2909193 := by
    simpa [prefixWord, tailWord_2909193, baseEnd_2909193] using wordTrace_append hprefix tailTrace_2909193
  have hstable : (prefixWord ++ tailWord_2909193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909193).length < 2 ^ (prefixWord ++ tailWord_2909193).sum := by decide
  have hdescent : baseEnd_2909193 < baseStart_2909193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909209 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2909209 : Nat := 118140960795 + 2909209 * 2 ^ 59
def prefixEnd_2909209 : Nat := 4983230072969 + 3 ^ 40 * 2909209 * 2
def baseEnd_2909209 : Nat := 1493822541386013440108297

theorem tailTrace_2909209 : CollatzResearch.WordTrace tailWord_2909209 prefixEnd_2909209 1493822541386013440108297 := by
  unfold tailWord_2909209
  simp only [CollatzResearch.WordTrace]
  refine ⟨106107569317440121185794681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70738379544960080790529787 106107569317440121185794681)
  ·
    refine ⟨79580676988080090889346011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106107569317440121185794681 79580676988080090889346011)
    ·
      refine ⟨119371015482120136334019017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79580676988080090889346011 119371015482120136334019017)
      ·
        refine ⟨89528261611590102250514263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119371015482120136334019017 89528261611590102250514263)
        ·
          refine ⟨134292392417385153375771395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89528261611590102250514263 134292392417385153375771395)
          ·
            refine ⟨201438588626077730063657093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134292392417385153375771395 201438588626077730063657093)
            ·
              refine ⟨37769735367389574386935705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201438588626077730063657093 37769735367389574386935705)
              ·
                refine ⟨28327301525542180790201779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37769735367389574386935705 28327301525542180790201779)
                ·
                  refine ⟨42490952288313271185302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28327301525542180790201779 42490952288313271185302669)
                  ·
                    refine ⟨15934107108117476694488501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42490952288313271185302669 15934107108117476694488501)
                    ·
                      refine ⟨1493822541386013440108297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15934107108117476694488501 1493822541386013440108297)
                      ·
                        rfl

theorem cell23_2909209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2909209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909209 prefixEnd_2909209 := by exact prefixLift 2909209
  have htrace : WordTrace (prefixWord ++ tailWord_2909209) baseStart_2909209 baseEnd_2909209 := by
    simpa [prefixWord, tailWord_2909209, baseEnd_2909209] using wordTrace_append hprefix tailTrace_2909209
  have hstable : (prefixWord ++ tailWord_2909209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909209).length < 2 ^ (prefixWord ++ tailWord_2909209).sum := by decide
  have hdescent : baseEnd_2909209 < baseStart_2909209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2909239 : Nat := 118140960795 + 2909239 * 2 ^ 59
def prefixEnd_2909239 : Nat := 4983230072969 + 3 ^ 40 * 2909239 * 2
def baseEnd_2909239 : Nat := 1493837945805648322733159

theorem tailTrace_2909239 : CollatzResearch.WordTrace tailWord_2909239 prefixEnd_2909239 1493837945805648322733159 := by
  unfold tailWord_2909239
  simp only [CollatzResearch.WordTrace]
  refine ⟨106108663507331436309386771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70739109004887624206257847 106108663507331436309386771)
  ·
    refine ⟨159162995260997154464080157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106108663507331436309386771 159162995260997154464080157)
    ·
      refine ⟨59686123222873932924030059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159162995260997154464080157 59686123222873932924030059)
      ·
        refine ⟨89529184834310899386045089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59686123222873932924030059 89529184834310899386045089)
        ·
          refine ⟨67146888625733174539533817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89529184834310899386045089 67146888625733174539533817)
          ·
            refine ⟨50360166469299880904650363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67146888625733174539533817 50360166469299880904650363)
            ·
              refine ⟨75540249703949821356975545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50360166469299880904650363 75540249703949821356975545)
              ·
                refine ⟨56655187277962366017731659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75540249703949821356975545 56655187277962366017731659)
                ·
                  refine ⟨84982780916943549026597489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56655187277962366017731659 84982780916943549026597489)
                  ·
                    refine ⟨63737085687707661769948117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84982780916943549026597489 63737085687707661769948117)
                    ·
                      refine ⟨1493837945805648322733159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63737085687707661769948117 1493837945805648322733159)
                      ·
                        rfl

theorem cell23_2909239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2909239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909239 prefixEnd_2909239 := by exact prefixLift 2909239
  have htrace : WordTrace (prefixWord ++ tailWord_2909239) baseStart_2909239 baseEnd_2909239 := by
    simpa [prefixWord, tailWord_2909239, baseEnd_2909239] using wordTrace_append hprefix tailTrace_2909239
  have hstable : (prefixWord ++ tailWord_2909239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909239).length < 2 ^ (prefixWord ++ tailWord_2909239).sum := by decide
  have hdescent : baseEnd_2909239 < baseStart_2909239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909256 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_2909256 : Nat := 118140960795 + 2909256 * 2 ^ 59
def prefixEnd_2909256 : Nat := 4983230072969 + 3 ^ 40 * 2909256 * 2
def baseEnd_2909256 : Nat := 1493846674976774756220581

theorem tailTrace_2909256 : CollatzResearch.WordTrace tailWord_2909256 prefixEnd_2909256 1493846674976774756220581 := by
  unfold tailWord_2909256
  simp only [CollatzResearch.WordTrace]
  refine ⟨53054641774134924106377811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70739522365513232141837081 53054641774134924106377811)
  ·
    refine ⟨79581962661202386159566717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53054641774134924106377811 79581962661202386159566717)
    ·
      refine ⟨29843235997950894809837519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79581962661202386159566717 29843235997950894809837519)
      ·
        refine ⟨44764853996926342214756279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29843235997950894809837519 44764853996926342214756279)
        ·
          refine ⟨67147280995389513322134419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44764853996926342214756279 67147280995389513322134419)
          ·
            refine ⟨100720921493084269983201629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67147280995389513322134419 100720921493084269983201629)
            ·
              refine ⟨37770345559906601243700611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100720921493084269983201629 37770345559906601243700611)
              ·
                refine ⟨56655518339859901865550917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37770345559906601243700611 56655518339859901865550917)
                ·
                  refine ⟨10622909688723731599790797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56655518339859901865550917 10622909688723731599790797)
                  ·
                    refine ⟨3983591133271399349921549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10622909688723731599790797 3983591133271399349921549)
                    ·
                      refine ⟨1493846674976774756220581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983591133271399349921549 1493846674976774756220581)
                      ·
                        rfl

theorem cell23_2909256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_2909256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909256 prefixEnd_2909256 := by exact prefixLift 2909256
  have htrace : WordTrace (prefixWord ++ tailWord_2909256) baseStart_2909256 baseEnd_2909256 := by
    simpa [prefixWord, tailWord_2909256, baseEnd_2909256] using wordTrace_append hprefix tailTrace_2909256
  have hstable : (prefixWord ++ tailWord_2909256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909256).length < 2 ^ (prefixWord ++ tailWord_2909256).sum := by decide
  have hdescent : baseEnd_2909256 < baseStart_2909256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909259 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 7]
def baseStart_2909259 : Nat := 118140960795 + 2909259 * 2 ^ 59
def prefixEnd_2909259 : Nat := 4983230072969 + 3 ^ 40 * 2909259 * 2
def baseEnd_2909259 : Nat := 497949405139579414827689

theorem tailTrace_2909259 : CollatzResearch.WordTrace tailWord_2909259 prefixEnd_2909259 497949405139579414827689 := by
  unfold tailWord_2909259
  simp only [CollatzResearch.WordTrace]
  refine ⟨106109392967258979725114831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70739595311505986483409887 106109392967258979725114831)
  ·
    refine ⟨159164089450888469587672247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106109392967258979725114831 159164089450888469587672247)
    ·
      refine ⟨238746134176332704381508371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159164089450888469587672247 238746134176332704381508371)
      ·
        refine ⟨358119201264499056572262557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238746134176332704381508371 358119201264499056572262557)
        ·
          refine ⟨134294700474187146214598459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358119201264499056572262557 134294700474187146214598459)
          ·
            refine ⟨201442050711280719321897689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134294700474187146214598459 201442050711280719321897689)
            ·
              refine ⟨151081538033460539491423267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201442050711280719321897689 151081538033460539491423267)
              ·
                refine ⟨226622307050190809237134901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151081538033460539491423267 226622307050190809237134901)
                ·
                  refine ⟨21245841285955388365981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226622307050190809237134901 21245841285955388365981397)
                  ·
                    refine ⟨497949405139579414827689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21245841285955388365981397 497949405139579414827689)
                    ·
                      rfl

theorem cell23_2909259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_2909259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909259 prefixEnd_2909259 := by exact prefixLift 2909259
  have htrace : WordTrace (prefixWord ++ tailWord_2909259) baseStart_2909259 baseEnd_2909259 := by
    simpa [prefixWord, tailWord_2909259, baseEnd_2909259] using wordTrace_append hprefix tailTrace_2909259
  have hstable : (prefixWord ++ tailWord_2909259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909259).length < 2 ^ (prefixWord ++ tailWord_2909259).sum := by decide
  have hdescent : baseEnd_2909259 < baseStart_2909259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909276 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2909276 : Nat := 118140960795 + 2909276 * 2 ^ 59
def prefixEnd_2909276 : Nat := 4983230072969 + 3 ^ 40 * 2909276 * 2
def baseEnd_2909276 : Nat := 497952314863288225990163

theorem tailTrace_2909276 : CollatzResearch.WordTrace tailWord_2909276 prefixEnd_2909276 497952314863288225990163 := by
  unfold tailWord_2909276
  simp only [CollatzResearch.WordTrace]
  refine ⟨53055006504098695814241841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70740008672131594418989121 53055006504098695814241841)
  ·
    refine ⟨39791254878074021860681381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53055006504098695814241841 39791254878074021860681381)
    ·
      refine ⟨7460860289638879098877759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39791254878074021860681381 7460860289638879098877759)
      ·
        refine ⟨11191290434458318648316639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460860289638879098877759 11191290434458318648316639)
        ·
          refine ⟨16786935651687477972474959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191290434458318648316639 16786935651687477972474959)
          ·
            refine ⟨25180403477531216958712439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16786935651687477972474959 25180403477531216958712439)
            ·
              refine ⟨37770605216296825438068659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25180403477531216958712439 37770605216296825438068659)
              ·
                refine ⟨56655907824445238157102989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37770605216296825438068659 56655907824445238157102989)
                ·
                  refine ⟨21245965434166964308913621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56655907824445238157102989 21245965434166964308913621)
                  ·
                    refine ⟨497952314863288225990163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21245965434166964308913621 497952314863288225990163)
                    ·
                      rfl

theorem cell23_2909276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2909276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909276 prefixEnd_2909276 := by exact prefixLift 2909276
  have htrace : WordTrace (prefixWord ++ tailWord_2909276) baseStart_2909276 baseEnd_2909276 := by
    simpa [prefixWord, tailWord_2909276, baseEnd_2909276] using wordTrace_append hprefix tailTrace_2909276
  have hstable : (prefixWord ++ tailWord_2909276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909276).length < 2 ^ (prefixWord ++ tailWord_2909276).sum := by decide
  have hdescent : baseEnd_2909276 < baseStart_2909276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909296 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_2909296 : Nat := 118140960795 + 2909296 * 2 ^ 59
def prefixEnd_2909296 : Nat := 4983230072969 + 3 ^ 40 * 2909296 * 2
def baseEnd_2909296 : Nat := 1493867214202954599720397

theorem tailTrace_2909296 : CollatzResearch.WordTrace tailWord_2909296 prefixEnd_2909296 1493867214202954599720397 := by
  unfold tailWord_2909296
  simp only [CollatzResearch.WordTrace]
  refine ⟨53055371234062467522105871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70740494978749956696141161 53055371234062467522105871)
  ·
    refine ⟨79583056851093701283158807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53055371234062467522105871 79583056851093701283158807)
    ·
      refine ⟨119374585276640551924738211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79583056851093701283158807 119374585276640551924738211)
      ·
        refine ⟨179061877914960827887107317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119374585276640551924738211 179061877914960827887107317)
        ·
          refine ⟨16787051054527577614416311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179061877914960827887107317 16787051054527577614416311)
          ·
            refine ⟨25180576581791366421624467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16787051054527577614416311 25180576581791366421624467)
            ·
              refine ⟨37770864872687049632436701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25180576581791366421624467 37770864872687049632436701)
              ·
                refine ⟨14164074327257643612163763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37770864872687049632436701 14164074327257643612163763)
                ·
                  refine ⟨21246111490886465418245645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14164074327257643612163763 21246111490886465418245645)
                  ·
                    refine ⟨7967291809082424531842117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21246111490886465418245645 7967291809082424531842117)
                    ·
                      refine ⟨1493867214202954599720397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7967291809082424531842117 1493867214202954599720397)
                      ·
                        rfl

theorem cell23_2909296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_2909296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909296 prefixEnd_2909296 := by exact prefixLift 2909296
  have htrace : WordTrace (prefixWord ++ tailWord_2909296) baseStart_2909296 baseEnd_2909296 := by
    simpa [prefixWord, tailWord_2909296, baseEnd_2909296] using wordTrace_append hprefix tailTrace_2909296
  have hstable : (prefixWord ++ tailWord_2909296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909296).length < 2 ^ (prefixWord ++ tailWord_2909296).sum := by decide
  have hdescent : baseEnd_2909296 < baseStart_2909296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909313 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2909313 : Nat := 118140960795 + 2909313 * 2 ^ 59
def prefixEnd_2909313 : Nat := 4983230072969 + 3 ^ 40 * 2909313 * 2
def baseEnd_2909313 : Nat := 1493875943374081033207819

theorem tailTrace_2909313 : CollatzResearch.WordTrace tailWord_2909313 prefixEnd_2909313 1493875943374081033207819 := by
  unfold tailWord_2909313
  simp only [CollatzResearch.WordTrace]
  refine ⟨106111362509063346947580593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70740908339375564631720395 106111362509063346947580593)
  ·
    refine ⟨79583521881797510210685445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106111362509063346947580593 79583521881797510210685445)
    ·
      refine ⟨14921910352837033164503521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79583521881797510210685445 14921910352837033164503521)
      ·
        refine ⟨11191432764627774873377641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921910352837033164503521 11191432764627774873377641)
        ·
          refine ⟨8393574573470831155033231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11191432764627774873377641 8393574573470831155033231)
          ·
            refine ⟨12590361860206246732549847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393574573470831155033231 12590361860206246732549847)
            ·
              refine ⟨18885542790309370098824771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590361860206246732549847 18885542790309370098824771)
              ·
                refine ⟨28328314185464055148237157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18885542790309370098824771 28328314185464055148237157)
                ·
                  refine ⟨5311558909774510340294467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28328314185464055148237157 5311558909774510340294467)
                  ·
                    refine ⟨7967338364661765510441701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5311558909774510340294467 7967338364661765510441701)
                    ·
                      refine ⟨1493875943374081033207819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7967338364661765510441701 1493875943374081033207819)
                      ·
                        rfl

theorem cell23_2909313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2909313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909313 prefixEnd_2909313 := by exact prefixLift 2909313
  have htrace : WordTrace (prefixWord ++ tailWord_2909313) baseStart_2909313 baseEnd_2909313 := by
    simpa [prefixWord, tailWord_2909313, baseEnd_2909313] using wordTrace_append hprefix tailTrace_2909313
  have hstable : (prefixWord ++ tailWord_2909313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909313).length < 2 ^ (prefixWord ++ tailWord_2909313).sum := by decide
  have hdescent : baseEnd_2909313 < baseStart_2909313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909374 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2909374 : Nat := 118140960795 + 2909374 * 2 ^ 59
def prefixEnd_2909374 : Nat := 4983230072969 + 3 ^ 40 * 2909374 * 2
def baseEnd_2909374 : Nat := 497969088564668431515013

theorem tailTrace_2909374 : CollatzResearch.WordTrace tailWord_2909374 prefixEnd_2909374 497969088564668431515013 := by
  unfold tailWord_2909374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264198420230294295693897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70742391574561569577034117 13264198420230294295693897)
  ·
    refine ⟨9948148815172720721770423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13264198420230294295693897 9948148815172720721770423)
    ·
      refine ⟨14922223222759081082655635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9948148815172720721770423 14922223222759081082655635)
      ·
        refine ⟨22383334834138621623983453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14922223222759081082655635 22383334834138621623983453)
        ·
          refine ⟨8393750562801983108993795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22383334834138621623983453 8393750562801983108993795)
          ·
            refine ⟨12590625844202974663490693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393750562801983108993795 12590625844202974663490693)
            ·
              refine ⟨2360742345788057749404505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12590625844202974663490693 2360742345788057749404505)
              ·
                refine ⟨1770556759341043312053379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360742345788057749404505 1770556759341043312053379)
                ·
                  refine ⟨2655835139011564968080069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770556759341043312053379 2655835139011564968080069)
                  ·
                    refine ⟨497969088564668431515013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655835139011564968080069 497969088564668431515013)
                    ·
                      rfl

theorem cell23_2909374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2909374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909374 prefixEnd_2909374 := by exact prefixLift 2909374
  have htrace : WordTrace (prefixWord ++ tailWord_2909374) baseStart_2909374 baseEnd_2909374 := by
    simpa [prefixWord, tailWord_2909374, baseEnd_2909374] using wordTrace_append hprefix tailTrace_2909374
  have hstable : (prefixWord ++ tailWord_2909374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909374).length < 2 ^ (prefixWord ++ tailWord_2909374).sum := by decide
  have hdescent : baseEnd_2909374 < baseStart_2909374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909397 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2909397 : Nat := 118140960795 + 2909397 * 2 ^ 59
def prefixEnd_2909397 : Nat := 4983230072969 + 3 ^ 40 * 2909397 * 2
def baseEnd_2909397 : Nat := 1493919075749058704557433

theorem tailTrace_2909397 : CollatzResearch.WordTrace tailWord_2909397 prefixEnd_2909397 1493919075749058704557433 := by
  unfold tailWord_2909397
  simp only [CollatzResearch.WordTrace]
  refine ⟨106114426240759029293638445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70742950827172686195758963 106114426240759029293638445)
  ·
    refine ⟨39792909840284635985114417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106114426240759029293638445 39792909840284635985114417)
    ·
      refine ⟨29844682380213476988835813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39792909840284635985114417 29844682380213476988835813)
      ·
        refine ⟨5595877946290026935406715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29844682380213476988835813 5595877946290026935406715)
        ·
          refine ⟨8393816919435040403110073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595877946290026935406715 8393816919435040403110073)
          ·
            refine ⟨6295362689576280302332555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8393816919435040403110073 6295362689576280302332555)
            ·
              refine ⟨9443044034364420453498833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295362689576280302332555 9443044034364420453498833)
              ·
                refine ⟨7082283025773315340124125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9443044034364420453498833 7082283025773315340124125)
                ·
                  refine ⟨2655856134664993252546547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7082283025773315340124125 2655856134664993252546547)
                  ·
                    refine ⟨3983784201997489878819821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655856134664993252546547 3983784201997489878819821)
                    ·
                      refine ⟨1493919075749058704557433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3983784201997489878819821 1493919075749058704557433)
                      ·
                        rfl

theorem cell23_2909397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2909397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909397 prefixEnd_2909397 := by exact prefixLift 2909397
  have htrace : WordTrace (prefixWord ++ tailWord_2909397) baseStart_2909397 baseEnd_2909397 := by
    simpa [prefixWord, tailWord_2909397, baseEnd_2909397] using wordTrace_append hprefix tailTrace_2909397
  have hstable : (prefixWord ++ tailWord_2909397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909397).length < 2 ^ (prefixWord ++ tailWord_2909397).sum := by decide
  have hdescent : baseEnd_2909397 < baseStart_2909397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909420 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_2909420 : Nat := 118140960795 + 2909420 * 2 ^ 59
def prefixEnd_2909420 : Nat := 4983230072969 + 3 ^ 40 * 2909420 * 2
def baseEnd_2909420 : Nat := 1493930885804112114569827

theorem tailTrace_2909420 : CollatzResearch.WordTrace tailWord_2909420 prefixEnd_2909420 1493930885804112114569827 := by
  unfold tailWord_2909420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53057632559837852110862857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70743510079783802814483809 53057632559837852110862857)
  ·
    refine ⟨39793224419878389083147143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53057632559837852110862857 39793224419878389083147143)
    ·
      refine ⟨59689836629817583624720715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39793224419878389083147143 59689836629817583624720715)
      ·
        refine ⟨89534754944726375437081073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59689836629817583624720715 89534754944726375437081073)
        ·
          refine ⟨67151066208544781577810805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89534754944726375437081073 67151066208544781577810805)
          ·
            refine ⟨6295412457051073272919763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67151066208544781577810805 6295412457051073272919763)
            ·
              refine ⟨9443118685576609909379645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295412457051073272919763 9443118685576609909379645)
              ·
                refine ⟨3541169507091228716017367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9443118685576609909379645 3541169507091228716017367)
                ·
                  refine ⟨5311754260636843074026051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541169507091228716017367 5311754260636843074026051)
                  ·
                    refine ⟨7967631390955264611039077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5311754260636843074026051 7967631390955264611039077)
                    ·
                      refine ⟨1493930885804112114569827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7967631390955264611039077 1493930885804112114569827)
                      ·
                        rfl

theorem cell23_2909420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_2909420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909420 prefixEnd_2909420 := by exact prefixLift 2909420
  have htrace : WordTrace (prefixWord ++ tailWord_2909420) baseStart_2909420 baseEnd_2909420 := by
    simpa [prefixWord, tailWord_2909420, baseEnd_2909420] using wordTrace_append hprefix tailTrace_2909420
  have hstable : (prefixWord ++ tailWord_2909420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909420).length < 2 ^ (prefixWord ++ tailWord_2909420).sum := by decide
  have hdescent : baseEnd_2909420 < baseStart_2909420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_2909456 : Nat := 118140960795 + 2909456 * 2 ^ 59
def prefixEnd_2909456 : Nat := 4983230072969 + 3 ^ 40 * 2909456 * 2
def baseEnd_2909456 : Nat := 497983123702557991239887

theorem tailTrace_2909456 : CollatzResearch.WordTrace tailWord_2909456 prefixEnd_2909456 497983123702557991239887 := by
  unfold tailWord_2909456
  simp only [CollatzResearch.WordTrace]
  refine ⟨53058289073772641185018111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70744385431696854913357481 53058289073772641185018111)
  ·
    refine ⟨79587433610658961777527167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53058289073772641185018111 79587433610658961777527167)
    ·
      refine ⟨119381150415988442666290751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79587433610658961777527167 119381150415988442666290751)
      ·
        refine ⟨179071725623982663999436127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119381150415988442666290751 179071725623982663999436127)
        ·
          refine ⟨268607588435973995999154191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179071725623982663999436127 268607588435973995999154191)
          ·
            refine ⟨402911382653960993998731287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268607588435973995999154191 402911382653960993998731287)
            ·
              refine ⟨604367073980941490998096931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402911382653960993998731287 604367073980941490998096931)
              ·
                refine ⟨906550610971412236497145397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604367073980941490998096931 906550610971412236497145397)
                ·
                  refine ⟨84989119778569897171607381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 906550610971412236497145397 84989119778569897171607381)
                  ·
                    refine ⟨497983123702557991239887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84989119778569897171607381 497983123702557991239887)
                    ·
                      rfl

theorem cell23_2909456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_2909456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909456 prefixEnd_2909456 := by exact prefixLift 2909456
  have htrace : WordTrace (prefixWord ++ tailWord_2909456) baseStart_2909456 baseEnd_2909456 := by
    simpa [prefixWord, tailWord_2909456, baseEnd_2909456] using wordTrace_append hprefix tailTrace_2909456
  have hstable : (prefixWord ++ tailWord_2909456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909456).length < 2 ^ (prefixWord ++ tailWord_2909456).sum := by decide
  have hdescent : baseEnd_2909456 < baseStart_2909456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909513 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2909513 : Nat := 118140960795 + 2909513 * 2 ^ 59
def prefixEnd_2909513 : Nat := 4983230072969 + 3 ^ 40 * 2909513 * 2
def baseEnd_2909513 : Nat := 1493978639504980250706899

theorem tailTrace_2909513 : CollatzResearch.WordTrace tailWord_2909513 prefixEnd_2909513 1493978639504980250706899 := by
  unfold tailWord_2909513
  simp only [CollatzResearch.WordTrace]
  refine ⟨106118657108338781104861193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70745771405559187403240795 106118657108338781104861193)
  ·
    refine ⟨79588992831254085828645895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106118657108338781104861193 79588992831254085828645895)
    ·
      refine ⟨119383489246881128742968843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79588992831254085828645895 119383489246881128742968843)
      ·
        refine ⟨179075233870321693114453265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119383489246881128742968843 179075233870321693114453265)
        ·
          refine ⟨134306425402741269835839949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179075233870321693114453265 134306425402741269835839949)
          ·
            refine ⟨50364909526027976188439981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134306425402741269835839949 50364909526027976188439981)
            ·
              refine ⟨18886841072260491070664993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50364909526027976188439981 18886841072260491070664993)
              ·
                refine ⟨14165130804195368302998745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18886841072260491070664993 14165130804195368302998745)
                ·
                  refine ⟨10623848103146526227249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165130804195368302998745 10623848103146526227249059)
                  ·
                    refine ⟨15935772154719789340873589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10623848103146526227249059 15935772154719789340873589)
                    ·
                      refine ⟨1493978639504980250706899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15935772154719789340873589 1493978639504980250706899)
                      ·
                        rfl

theorem cell23_2909513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2909513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909513 prefixEnd_2909513 := by exact prefixLift 2909513
  have htrace : WordTrace (prefixWord ++ tailWord_2909513) baseStart_2909513 baseEnd_2909513 := by
    simpa [prefixWord, tailWord_2909513, baseEnd_2909513] using wordTrace_append hprefix tailTrace_2909513
  have hstable : (prefixWord ++ tailWord_2909513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909513).length < 2 ^ (prefixWord ++ tailWord_2909513).sum := by decide
  have hdescent : baseEnd_2909513 < baseStart_2909513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909527 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_2909527 : Nat := 118140960795 + 2909527 * 2 ^ 59
def prefixEnd_2909527 : Nat := 4983230072969 + 3 ^ 40 * 2909527 * 2
def baseEnd_2909527 : Nat := 1493985828234143195931835

theorem tailTrace_2909527 : CollatzResearch.WordTrace tailWord_2909527 prefixEnd_2909527 1493985828234143195931835 := by
  unfold tailWord_2909527
  simp only [CollatzResearch.WordTrace]
  refine ⟨106119167730288061495870835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70746111820192040997247223 106119167730288061495870835)
  ·
    refine ⟨159178751595432092243806253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106119167730288061495870835 159178751595432092243806253)
    ·
      refine ⟨59692031848287034591427345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159178751595432092243806253 59692031848287034591427345)
      ·
        refine ⟨44769023886215275943570509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59692031848287034591427345 44769023886215275943570509)
        ·
          refine ⟨16788383957330728478838941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44769023886215275943570509 16788383957330728478838941)
          ·
            refine ⟨6295643983999023179564603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16788383957330728478838941 6295643983999023179564603)
            ·
              refine ⟨9443465975998534769346905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295643983999023179564603 9443465975998534769346905)
              ·
                refine ⟨7082599481998901077010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9443465975998534769346905 7082599481998901077010179)
                ·
                  refine ⟨10623899222998351615515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7082599481998901077010179 10623899222998351615515269)
                  ·
                    refine ⟨1991981104312190927909113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10623899222998351615515269 1991981104312190927909113)
                    ·
                      refine ⟨1493985828234143195931835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1991981104312190927909113 1493985828234143195931835)
                      ·
                        rfl

theorem cell23_2909527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_2909527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909527 prefixEnd_2909527 := by exact prefixLift 2909527
  have htrace : WordTrace (prefixWord ++ tailWord_2909527) baseStart_2909527 baseEnd_2909527 := by
    simpa [prefixWord, tailWord_2909527, baseEnd_2909527] using wordTrace_append hprefix tailTrace_2909527
  have hstable : (prefixWord ++ tailWord_2909527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909527).length < 2 ^ (prefixWord ++ tailWord_2909527).sum := by decide
  have hdescent : baseEnd_2909527 < baseStart_2909527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909557 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2909557 : Nat := 118140960795 + 2909557 * 2 ^ 59
def prefixEnd_2909557 : Nat := 4983230072969 + 3 ^ 40 * 2909557 * 2
def baseEnd_2909557 : Nat := 1494001232653778078556697

theorem tailTrace_2909557 : CollatzResearch.WordTrace tailWord_2909557 prefixEnd_2909557 1494001232653778078556697 := by
  unfold tailWord_2909557
  simp only [CollatzResearch.WordTrace]
  refine ⟨106120261920179376619462925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70746841280119584412975283 106120261920179376619462925)
  ·
    refine ⟨39795098220067266232298597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106120261920179376619462925 39795098220067266232298597)
    ·
      refine ⟨7461580916262612418555987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39795098220067266232298597 7461580916262612418555987)
      ·
        refine ⟨11192371374393918627833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461580916262612418555987 11192371374393918627833981)
        ·
          refine ⟨4197139265397719485437743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11192371374393918627833981 4197139265397719485437743)
          ·
            refine ⟨6295708898096579228156615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197139265397719485437743 6295708898096579228156615)
            ·
              refine ⟨9443563347144868842234923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295708898096579228156615 9443563347144868842234923)
              ·
                refine ⟨14165345020717303263352385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443563347144868842234923 14165345020717303263352385)
                ·
                  refine ⟨10624008765537977447514289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165345020717303263352385 10624008765537977447514289)
                  ·
                    refine ⟨7968006574153483085635717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10624008765537977447514289 7968006574153483085635717)
                    ·
                      refine ⟨1494001232653778078556697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7968006574153483085635717 1494001232653778078556697)
                      ·
                        rfl

theorem cell23_2909557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2909557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909557 prefixEnd_2909557 := by exact prefixLift 2909557
  have htrace : WordTrace (prefixWord ++ tailWord_2909557) baseStart_2909557 baseEnd_2909557 := by
    simpa [prefixWord, tailWord_2909557, baseEnd_2909557] using wordTrace_append hprefix tailTrace_2909557
  have hstable : (prefixWord ++ tailWord_2909557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909557).length < 2 ^ (prefixWord ++ tailWord_2909557).sum := by decide
  have hdescent : baseEnd_2909557 < baseStart_2909557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909563 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 7]
def baseStart_2909563 : Nat := 118140960795 + 2909563 * 2 ^ 59
def prefixEnd_2909563 : Nat := 4983230072969 + 3 ^ 40 * 2909563 * 2
def baseEnd_2909563 : Nat := 498001437845901685027223

theorem tailTrace_2909563 : CollatzResearch.WordTrace tailWord_2909563 prefixEnd_2909563 498001437845901685027223 := by
  unfold tailWord_2909563
  simp only [CollatzResearch.WordTrace]
  refine ⟨106120480758157639644181343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70746987172105093096120895 106120480758157639644181343)
  ·
    refine ⟨159180721137236459466272015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106120480758157639644181343 159180721137236459466272015)
    ·
      refine ⟨238771081705854689199408023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159180721137236459466272015 238771081705854689199408023)
      ·
        refine ⟨358156622558782033799112035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238771081705854689199408023 358156622558782033799112035)
        ·
          refine ⟨537234933838173050698668053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358156622558782033799112035 537234933838173050698668053)
          ·
            refine ⟨25182887523664361751500065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 537234933838173050698668053 25182887523664361751500065)
            ·
              refine ⟨18887165642748271313625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25182887523664361751500065 18887165642748271313625049)
              ·
                refine ⟨14165374232061203485218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18887165642748271313625049 14165374232061203485218787)
                ·
                  refine ⟨21248061348091805227828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14165374232061203485218787 21248061348091805227828181)
                  ·
                    refine ⟨498001437845901685027223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21248061348091805227828181 498001437845901685027223)
                    ·
                      rfl

theorem cell23_2909563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_2909563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909563 prefixEnd_2909563 := by exact prefixLift 2909563
  have htrace : WordTrace (prefixWord ++ tailWord_2909563) baseStart_2909563 baseEnd_2909563 := by
    simpa [prefixWord, tailWord_2909563, baseEnd_2909563] using wordTrace_append hprefix tailTrace_2909563
  have hstable : (prefixWord ++ tailWord_2909563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909563).length < 2 ^ (prefixWord ++ tailWord_2909563).sum := by decide
  have hdescent : baseEnd_2909563 < baseStart_2909563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909573 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2909573 : Nat := 118140960795 + 2909573 * 2 ^ 59
def prefixEnd_2909573 : Nat := 4983230072969 + 3 ^ 40 * 2909573 * 2
def baseEnd_2909573 : Nat := 1494009448344250015956623

theorem tailTrace_2909573 : CollatzResearch.WordTrace tailWord_2909573 prefixEnd_2909573 1494009448344250015956623 := by
  unfold tailWord_2909573
  simp only [CollatzResearch.WordTrace]
  refine ⟨106120845488121411352045373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70747230325414274234696915 106120845488121411352045373)
  ·
    refine ⟨39795317058045529257017015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106120845488121411352045373 39795317058045529257017015)
    ·
      refine ⟨59692975587068293885525523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39795317058045529257017015 59692975587068293885525523)
      ·
        refine ⟨89539463380602440828288285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59692975587068293885525523 89539463380602440828288285)
        ·
          refine ⟨33577298767725915310608107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89539463380602440828288285 33577298767725915310608107)
          ·
            refine ⟨50365948151588872965912161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33577298767725915310608107 50365948151588872965912161)
            ·
              refine ⟨37774461113691654724434121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50365948151588872965912161 37774461113691654724434121)
              ·
                refine ⟨28330845835268741043325591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37774461113691654724434121 28330845835268741043325591)
                ·
                  refine ⟨42496268752903111564988387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28330845835268741043325591 42496268752903111564988387)
                  ·
                    refine ⟨63744403129354667347482581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42496268752903111564988387 63744403129354667347482581)
                    ·
                      refine ⟨1494009448344250015956623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63744403129354667347482581 1494009448344250015956623)
                      ·
                        rfl

theorem cell23_2909573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2909573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909573 prefixEnd_2909573 := by exact prefixLift 2909573
  have htrace : WordTrace (prefixWord ++ tailWord_2909573) baseStart_2909573 baseEnd_2909573 := by
    simpa [prefixWord, tailWord_2909573, baseEnd_2909573] using wordTrace_append hprefix tailTrace_2909573
  have hstable : (prefixWord ++ tailWord_2909573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909573).length < 2 ^ (prefixWord ++ tailWord_2909573).sum := by decide
  have hdescent : baseEnd_2909573 < baseStart_2909573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909600 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2909600 : Nat := 118140960795 + 2909600 * 2 ^ 59
def prefixEnd_2909600 : Nat := 4983230072969 + 3 ^ 40 * 2909600 * 2
def baseEnd_2909600 : Nat := 1494023312321921410318999

theorem tailTrace_2909600 : CollatzResearch.WordTrace tailWord_2909600 prefixEnd_2909600 1494023312321921410318999 := by
  unfold tailWord_2909600
  simp only [CollatzResearch.WordTrace]
  refine ⟨53060915129511797481639127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70747886839349063308852169 53060915129511797481639127)
  ·
    refine ⟨79591372694267696222458691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53060915129511797481639127 79591372694267696222458691)
    ·
      refine ⟨119387059041401544333688037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79591372694267696222458691 119387059041401544333688037)
      ·
        refine ⟨22385073570262789562566507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119387059041401544333688037 22385073570262789562566507)
        ·
          refine ⟨33577610355394184343849761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22385073570262789562566507 33577610355394184343849761)
          ·
            refine ⟨25183207766545638257887321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33577610355394184343849761 25183207766545638257887321)
            ·
              refine ⟨18887405824909228693415491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25183207766545638257887321 18887405824909228693415491)
              ·
                refine ⟨28331108737363843040123237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887405824909228693415491 28331108737363843040123237)
                ·
                  refine ⟨5312082888255720570023107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28331108737363843040123237 5312082888255720570023107)
                  ·
                    refine ⟨7968124332383580855034661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312082888255720570023107 7968124332383580855034661)
                    ·
                      refine ⟨1494023312321921410318999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7968124332383580855034661 1494023312321921410318999)
                      ·
                        rfl

theorem cell23_2909600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2909600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909600 prefixEnd_2909600 := by exact prefixLift 2909600
  have htrace : WordTrace (prefixWord ++ tailWord_2909600) baseStart_2909600 baseEnd_2909600 := by
    simpa [prefixWord, tailWord_2909600, baseEnd_2909600] using wordTrace_append hprefix tailTrace_2909600
  have hstable : (prefixWord ++ tailWord_2909600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909600).length < 2 ^ (prefixWord ++ tailWord_2909600).sum := by decide
  have hdescent : baseEnd_2909600 < baseStart_2909600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909617 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2909617 : Nat := 118140960795 + 2909617 * 2 ^ 59
def prefixEnd_2909617 : Nat := 4983230072969 + 3 ^ 40 * 2909617 * 2
def baseEnd_2909617 : Nat := 1494032041493047843806421

theorem tailTrace_2909617 : CollatzResearch.WordTrace tailWord_2909617 prefixEnd_2909617 1494032041493047843806421 := by
  unfold tailWord_2909617
  simp only [CollatzResearch.WordTrace]
  refine ⟨106122450299962006866647105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70748300199974671244431403 106122450299962006866647105)
  ·
    refine ⟨79591837724971505149985329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106122450299962006866647105 79591837724971505149985329)
    ·
      refine ⟨59693878293728628862488997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79591837724971505149985329 59693878293728628862488997)
      ·
        refine ⟨11192602180074117911716687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59693878293728628862488997 11192602180074117911716687)
        ·
          refine ⟨16788903270111176867575031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192602180074117911716687 16788903270111176867575031)
          ·
            refine ⟨25183354905166765301362547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16788903270111176867575031 25183354905166765301362547)
            ·
              refine ⟨37775032357750147952043821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183354905166765301362547 37775032357750147952043821)
              ·
                refine ⟨14165637134156305482016433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37775032357750147952043821 14165637134156305482016433)
                ·
                  refine ⟨10624227850617229111512325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14165637134156305482016433 10624227850617229111512325)
                  ·
                    refine ⟨1992042721990730458408561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10624227850617229111512325 1992042721990730458408561)
                    ·
                      refine ⟨1494032041493047843806421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992042721990730458408561 1494032041493047843806421)
                      ·
                        rfl

theorem cell23_2909617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2909617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909617 prefixEnd_2909617 := by exact prefixLift 2909617
  have htrace : WordTrace (prefixWord ++ tailWord_2909617) baseStart_2909617 baseEnd_2909617 := by
    simpa [prefixWord, tailWord_2909617, baseEnd_2909617] using wordTrace_append hprefix tailTrace_2909617
  have hstable : (prefixWord ++ tailWord_2909617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909617).length < 2 ^ (prefixWord ++ tailWord_2909617).sum := by decide
  have hdescent : baseEnd_2909617 < baseStart_2909617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909630 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2909630 : Nat := 118140960795 + 2909630 * 2 ^ 59
def prefixEnd_2909630 : Nat := 4983230072969 + 3 ^ 40 * 2909630 * 2
def baseEnd_2909630 : Nat := 1494038716741556292943861

theorem tailTrace_2909630 : CollatzResearch.WordTrace tailWord_2909630 prefixEnd_2909630 1494038716741556292943861 := by
  unfold tailWord_2909630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13265365556114363760858793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70748616299276606724580229 13265365556114363760858793)
  ·
    refine ⟨9949024167085772820644095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13265365556114363760858793 9949024167085772820644095)
    ·
      refine ⟨14923536250628659230966143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9949024167085772820644095 14923536250628659230966143)
      ·
        refine ⟨22385304375942988846449215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14923536250628659230966143 22385304375942988846449215)
        ·
          refine ⟨33577956563914483269673823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22385304375942988846449215 33577956563914483269673823)
          ·
            refine ⟨50366934845871724904510735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33577956563914483269673823 50366934845871724904510735)
            ·
              refine ⟨75550402268807587356766103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50366934845871724904510735 75550402268807587356766103)
              ·
                refine ⟨113325603403211381035149155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75550402268807587356766103 113325603403211381035149155)
                ·
                  refine ⟨169988405104817071552723733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113325603403211381035149155 169988405104817071552723733)
                  ·
                    refine ⟨7968206489288300229033925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169988405104817071552723733 7968206489288300229033925)
                    ·
                      refine ⟨1494038716741556292943861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7968206489288300229033925 1494038716741556292943861)
                      ·
                        rfl

theorem cell23_2909630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2909630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909630 prefixEnd_2909630 := by exact prefixLift 2909630
  have htrace : WordTrace (prefixWord ++ tailWord_2909630) baseStart_2909630 baseEnd_2909630 := by
    simpa [prefixWord, tailWord_2909630, baseEnd_2909630] using wordTrace_append hprefix tailTrace_2909630
  have hstable : (prefixWord ++ tailWord_2909630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909630).length < 2 ^ (prefixWord ++ tailWord_2909630).sum := by decide
  have hdescent : baseEnd_2909630 < baseStart_2909630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909654 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2909654 : Nat := 118140960795 + 2909654 * 2 ^ 59
def prefixEnd_2909654 : Nat := 4983230072969 + 3 ^ 40 * 2909654 * 2
def baseEnd_2909654 : Nat := 1494051040277264199043751

theorem tailTrace_2909654 : CollatzResearch.WordTrace tailWord_2909654 prefixEnd_2909654 1494051040277264199043751 := by
  unfold tailWord_2909654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632737487551747636609001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70749199867218641457162677 6632737487551747636609001)
  ·
    refine ⟨4974553115663810727456751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6632737487551747636609001 4974553115663810727456751)
    ·
      refine ⟨7461829673495716091185127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974553115663810727456751 7461829673495716091185127)
      ·
        refine ⟨11192744510243574136777691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461829673495716091185127 11192744510243574136777691)
        ·
          refine ⟨16789116765365361205166537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192744510243574136777691 16789116765365361205166537)
          ·
            refine ⟨12591837574024020903874903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16789116765365361205166537 12591837574024020903874903)
            ·
              refine ⟨18887756361036031355812355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591837574024020903874903 18887756361036031355812355)
              ·
                refine ⟨28331634541554047033718533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887756361036031355812355 28331634541554047033718533)
                ·
                  refine ⟨5312181476541383818822225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28331634541554047033718533 5312181476541383818822225)
                  ·
                    refine ⟨3984136107406037864116669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312181476541383818822225 3984136107406037864116669)
                    ·
                      refine ⟨1494051040277264199043751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984136107406037864116669 1494051040277264199043751)
                      ·
                        rfl

theorem cell23_2909654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2909654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909654 prefixEnd_2909654 := by exact prefixLift 2909654
  have htrace : WordTrace (prefixWord ++ tailWord_2909654) baseStart_2909654 baseEnd_2909654 := by
    simpa [prefixWord, tailWord_2909654, baseEnd_2909654] using wordTrace_append hprefix tailTrace_2909654
  have hstable : (prefixWord ++ tailWord_2909654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909654).length < 2 ^ (prefixWord ++ tailWord_2909654).sum := by decide
  have hdescent : baseEnd_2909654 < baseStart_2909654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909727 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_2909727 : Nat := 118140960795 + 2909727 * 2 ^ 59
def prefixEnd_2909727 : Nat := 4983230072969 + 3 ^ 40 * 2909727 * 2
def baseEnd_2909727 : Nat := 1494088524365042413430915

theorem tailTrace_2909727 : CollatzResearch.WordTrace tailWord_2909727 prefixEnd_2909727 1494088524365042413430915 := by
  unfold tailWord_2909727
  simp only [CollatzResearch.WordTrace]
  refine ⟨106126462329563495653151435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70750974886375663768767623 106126462329563495653151435)
  ·
    refine ⟨159189693494345243479727153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106126462329563495653151435 159189693494345243479727153)
    ·
      refine ⟨119392270120758932609795365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159189693494345243479727153 119392270120758932609795365)
      ·
        refine ⟨22386050647642299864336631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119392270120758932609795365 22386050647642299864336631)
        ·
          refine ⟨33579075971463449796504947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22386050647642299864336631 33579075971463449796504947)
          ·
            refine ⟨50368613957195174694757421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33579075971463449796504947 50368613957195174694757421)
            ·
              refine ⟨18888230233948190510534033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50368613957195174694757421 18888230233948190510534033)
              ·
                refine ⟨14166172675461142882900525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18888230233948190510534033 14166172675461142882900525)
                ·
                  refine ⟨5312314753297928581087697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14166172675461142882900525 5312314753297928581087697)
                  ·
                    refine ⟨3984236064973446435815773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312314753297928581087697 3984236064973446435815773)
                    ·
                      refine ⟨1494088524365042413430915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984236064973446435815773 1494088524365042413430915)
                      ·
                        rfl

theorem cell23_2909727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_2909727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909727 prefixEnd_2909727 := by exact prefixLift 2909727
  have htrace : WordTrace (prefixWord ++ tailWord_2909727) baseStart_2909727 baseEnd_2909727 := by
    simpa [prefixWord, tailWord_2909727, baseEnd_2909727] using wordTrace_append hprefix tailTrace_2909727
  have hstable : (prefixWord ++ tailWord_2909727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909727).length < 2 ^ (prefixWord ++ tailWord_2909727).sum := by decide
  have hdescent : baseEnd_2909727 < baseStart_2909727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909747 : List Nat := [1, 1, 1, 2, 4, 4, 3, 7]
def baseStart_2909747 : Nat := 118140960795 + 2909747 * 2 ^ 59
def prefixEnd_2909747 : Nat := 4983230072969 + 3 ^ 40 * 2909747 * 2
def baseEnd_2909747 : Nat := 55336992369560456858549

theorem tailTrace_2909747 : CollatzResearch.WordTrace tailWord_2909747 prefixEnd_2909747 55336992369560456858549 := by
  unfold tailWord_2909747
  simp only [CollatzResearch.WordTrace]
  refine ⟨106127191789491039068879495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70751461192994026045919663 106127191789491039068879495)
  ·
    refine ⟨159190787684236558603319243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106127191789491039068879495 159190787684236558603319243)
    ·
      refine ⟨238786181526354837904978865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159190787684236558603319243 238786181526354837904978865)
      ·
        refine ⟨179089636144766128428734149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238786181526354837904978865 179089636144766128428734149)
        ·
          refine ⟨33579306777143649080387653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179089636144766128428734149 33579306777143649080387653)
          ·
            refine ⟨6296120020714434202572685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33579306777143649080387653 6296120020714434202572685)
            ·
              refine ⟨2361045007767912825964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6296120020714434202572685 2361045007767912825964757)
              ·
                refine ⟨55336992369560456858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2361045007767912825964757 55336992369560456858549)
                ·
                  rfl

theorem cell23_2909747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 7].length) (baseStart_2909747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909747 prefixEnd_2909747 := by exact prefixLift 2909747
  have htrace : WordTrace (prefixWord ++ tailWord_2909747) baseStart_2909747 baseEnd_2909747 := by
    simpa [prefixWord, tailWord_2909747, baseEnd_2909747] using wordTrace_append hprefix tailTrace_2909747
  have hstable : (prefixWord ++ tailWord_2909747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909747).length < 2 ^ (prefixWord ++ tailWord_2909747).sum := by decide
  have hdescent : baseEnd_2909747 < baseStart_2909747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909817 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2909817 : Nat := 118140960795 + 2909817 * 2 ^ 59
def prefixEnd_2909817 : Nat := 4983230072969 + 3 ^ 40 * 2909817 * 2
def baseEnd_2909817 : Nat := 1494134737623947061305501

theorem tailTrace_2909817 : CollatzResearch.WordTrace tailWord_2909817 prefixEnd_2909817 1494134737623947061305501 := by
  unfold tailWord_2909817
  simp only [CollatzResearch.WordTrace]
  refine ⟨106129744899237441023927705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70753163266158294015951803 106129744899237441023927705)
  ·
    refine ⟨79597308674428080767945779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106129744899237441023927705 79597308674428080767945779)
    ·
      refine ⟨119395963011642121151918669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79597308674428080767945779 119395963011642121151918669)
      ·
        refine ⟨44773486129365795431969501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119395963011642121151918669 44773486129365795431969501)
        ·
          refine ⟨16790057298512173286988563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44773486129365795431969501 16790057298512173286988563)
          ·
            refine ⟨25185085947768259930482845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16790057298512173286988563 25185085947768259930482845)
            ·
              refine ⟨9444407230413097473931067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25185085947768259930482845 9444407230413097473931067)
              ·
                refine ⟨14166610845619646210896601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444407230413097473931067 14166610845619646210896601)
                ·
                  refine ⟨10624958134214734658172451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14166610845619646210896601 10624958134214734658172451)
                  ·
                    refine ⟨15937437201322101987258677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10624958134214734658172451 15937437201322101987258677)
                    ·
                      refine ⟨1494134737623947061305501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15937437201322101987258677 1494134737623947061305501)
                      ·
                        rfl

theorem cell23_2909817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2909817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909817 prefixEnd_2909817 := by exact prefixLift 2909817
  have htrace : WordTrace (prefixWord ++ tailWord_2909817) baseStart_2909817 baseEnd_2909817 := by
    simpa [prefixWord, tailWord_2909817, baseEnd_2909817] using wordTrace_append hprefix tailTrace_2909817
  have hstable : (prefixWord ++ tailWord_2909817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909817).length < 2 ^ (prefixWord ++ tailWord_2909817).sum := by decide
  have hdescent : baseEnd_2909817 < baseStart_2909817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909831 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_2909831 : Nat := 118140960795 + 2909831 * 2 ^ 59
def prefixEnd_2909831 : Nat := 4983230072969 + 3 ^ 40 * 2909831 * 2
def baseEnd_2909831 : Nat := 1494141926353110006530437

theorem tailTrace_2909831 : CollatzResearch.WordTrace tailWord_2909831 prefixEnd_2909831 1494141926353110006530437 := by
  unfold tailWord_2909831
  simp only [CollatzResearch.WordTrace]
  refine ⟨106130255521186721414937347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70753503680791147609958231 106130255521186721414937347)
  ·
    refine ⟨159195383281780082122406021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106130255521186721414937347 159195383281780082122406021)
    ·
      refine ⟨29849134365333765397951129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159195383281780082122406021 29849134365333765397951129)
      ·
        refine ⟨22386850774000324048463347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29849134365333765397951129 22386850774000324048463347)
        ·
          refine ⟨33580276161000486072695021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22386850774000324048463347 33580276161000486072695021)
          ·
            refine ⟨12592603560375182277260633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33580276161000486072695021 12592603560375182277260633)
            ·
              refine ⟨9444452670281386707945475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12592603560375182277260633 9444452670281386707945475)
              ·
                refine ⟨14166679005422080061918213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444452670281386707945475 14166679005422080061918213)
                ·
                  refine ⟨2656252313516640011609665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14166679005422080061918213 2656252313516640011609665)
                  ·
                    refine ⟨1992189235137480008707249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2656252313516640011609665 1992189235137480008707249)
                    ·
                      refine ⟨1494141926353110006530437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992189235137480008707249 1494141926353110006530437)
                      ·
                        rfl

theorem cell23_2909831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_2909831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909831 prefixEnd_2909831 := by exact prefixLift 2909831
  have htrace : WordTrace (prefixWord ++ tailWord_2909831) baseStart_2909831 baseEnd_2909831 := by
    simpa [prefixWord, tailWord_2909831, baseEnd_2909831] using wordTrace_append hprefix tailTrace_2909831
  have hstable : (prefixWord ++ tailWord_2909831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909831).length < 2 ^ (prefixWord ++ tailWord_2909831).sum := by decide
  have hdescent : baseEnd_2909831 < baseStart_2909831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909842 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2909842 : Nat := 118140960795 + 2909842 * 2 ^ 59
def prefixEnd_2909842 : Nat := 4983230072969 + 3 ^ 40 * 2909842 * 2
def baseEnd_2909842 : Nat := 1494147574640309463492887

theorem tailTrace_2909842 : CollatzResearch.WordTrace tailWord_2909842 prefixEnd_2909842 1494147574640309463492887 := by
  unfold tailWord_2909842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532664181036717573396945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70753771149431246862391853 26532664181036717573396945)
  ·
    refine ⟨19899498135777538180047709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26532664181036717573396945 19899498135777538180047709)
    ·
      refine ⟨7462311800916576817517891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19899498135777538180047709 7462311800916576817517891)
      ·
        refine ⟨11193467701374865226276837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462311800916576817517891 11193467701374865226276837)
        ·
          refine ⟨2098775194007787229926907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11193467701374865226276837 2098775194007787229926907)
          ·
            refine ⟨3148162791011680844890361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098775194007787229926907 3148162791011680844890361)
            ·
              refine ⟨2361122093258760633667771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148162791011680844890361 2361122093258760633667771)
              ·
                refine ⟨3541683139888140950501657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361122093258760633667771 3541683139888140950501657)
                ·
                  refine ⟨2656262354916105712876243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3541683139888140950501657 2656262354916105712876243)
                  ·
                    refine ⟨3984393532374158569314365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2656262354916105712876243 3984393532374158569314365)
                    ·
                      refine ⟨1494147574640309463492887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984393532374158569314365 1494147574640309463492887)
                      ·
                        rfl

theorem cell23_2909842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2909842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909842 prefixEnd_2909842 := by exact prefixLift 2909842
  have htrace : WordTrace (prefixWord ++ tailWord_2909842) baseStart_2909842 baseEnd_2909842 := by
    simpa [prefixWord, tailWord_2909842, baseEnd_2909842] using wordTrace_append hprefix tailTrace_2909842
  have hstable : (prefixWord ++ tailWord_2909842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909842).length < 2 ^ (prefixWord ++ tailWord_2909842).sum := by decide
  have hdescent : baseEnd_2909842 < baseStart_2909842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909848 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2909848 : Nat := 118140960795 + 2909848 * 2 ^ 59
def prefixEnd_2909848 : Nat := 4983230072969 + 3 ^ 40 * 2909848 * 2
def baseEnd_2909848 : Nat := 1494150655524236440017859

theorem tailTrace_2909848 : CollatzResearch.WordTrace tailWord_2909848 prefixEnd_2909848 1494150655524236440017859 := by
  unfold tailWord_2909848
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065437781062566659153099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70753917041416755545537465 53065437781062566659153099)
  ·
    refine ⟨79598156671593849988729649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53065437781062566659153099 79598156671593849988729649)
    ·
      refine ⟨59698617503695387491547237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79598156671593849988729649 59698617503695387491547237)
      ·
        refine ⟨11193490781942885154665107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59698617503695387491547237 11193490781942885154665107)
        ·
          refine ⟨16790236172914327731997661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193490781942885154665107 16790236172914327731997661)
          ·
            refine ⟨6296338564842872899499123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16790236172914327731997661 6296338564842872899499123)
            ·
              refine ⟨9444507847264309349248685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296338564842872899499123 9444507847264309349248685)
              ·
                refine ⟨3541690442724116005968257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9444507847264309349248685 3541690442724116005968257)
                ·
                  refine ⟨2656267832043087004476193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3541690442724116005968257 2656267832043087004476193)
                  ·
                    refine ⟨1992200874032315253357145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2656267832043087004476193 1992200874032315253357145)
                    ·
                      refine ⟨1494150655524236440017859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992200874032315253357145 1494150655524236440017859)
                      ·
                        rfl

theorem cell23_2909848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2909848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909848 prefixEnd_2909848 := by exact prefixLift 2909848
  have htrace : WordTrace (prefixWord ++ tailWord_2909848) baseStart_2909848 baseEnd_2909848 := by
    simpa [prefixWord, tailWord_2909848, baseEnd_2909848] using wordTrace_append hprefix tailTrace_2909848
  have hstable : (prefixWord ++ tailWord_2909848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909848).length < 2 ^ (prefixWord ++ tailWord_2909848).sum := by decide
  have hdescent : baseEnd_2909848 < baseStart_2909848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909884 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_2909884 : Nat := 118140960795 + 2909884 * 2 ^ 59
def prefixEnd_2909884 : Nat := 4983230072969 + 3 ^ 40 * 2909884 * 2
def baseEnd_2909884 : Nat := 498056380275932766389231

theorem tailTrace_2909884 : CollatzResearch.WordTrace tailWord_2909884 prefixEnd_2909884 498056380275932766389231 := by
  unfold tailWord_2909884
  simp only [CollatzResearch.WordTrace]
  refine ⟨53066094294997355733308353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70754792393329807644411137 53066094294997355733308353)
  ·
    refine ⟨39799570721248016799981265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53066094294997355733308353 39799570721248016799981265)
    ·
      refine ⟨29849678040936012599985949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39799570721248016799981265 29849678040936012599985949)
      ·
        refine ⟨11193629265351004724994731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29849678040936012599985949 11193629265351004724994731)
        ·
          refine ⟨16790443898026507087492097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193629265351004724994731 16790443898026507087492097)
          ·
            refine ⟨12592832923519880315619073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16790443898026507087492097 12592832923519880315619073)
            ·
              refine ⟨9444624692639910236714305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12592832923519880315619073 9444624692639910236714305)
              ·
                refine ⟨7083468519479932677535729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444624692639910236714305 7083468519479932677535729)
                ·
                  refine ⟨5312601389609949508151797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083468519479932677535729 5312601389609949508151797)
                  ·
                    refine ⟨498056380275932766389231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5312601389609949508151797 498056380275932766389231)
                    ·
                      rfl

theorem cell23_2909884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_2909884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909884 prefixEnd_2909884 := by exact prefixLift 2909884
  have htrace : WordTrace (prefixWord ++ tailWord_2909884) baseStart_2909884 baseEnd_2909884 := by
    simpa [prefixWord, tailWord_2909884, baseEnd_2909884] using wordTrace_append hprefix tailTrace_2909884
  have hstable : (prefixWord ++ tailWord_2909884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909884).length < 2 ^ (prefixWord ++ tailWord_2909884).sum := by decide
  have hdescent : baseEnd_2909884 < baseStart_2909884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3]
def baseStart_2909907 : Nat := 118140960795 + 2909907 * 2 ^ 59
def prefixEnd_2909907 : Nat := 4983230072969 + 3 ^ 40 * 2909907 * 2
def baseEnd_2909907 : Nat := 1494180950882851709180087

theorem tailTrace_2909907 : CollatzResearch.WordTrace tailWord_2909907 prefixEnd_2909907 1494180950882851709180087 := by
  unfold tailWord_2909907
  simp only [CollatzResearch.WordTrace]
  refine ⟨106133027468911386394703975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70755351645940924263135983 106133027468911386394703975)
  ·
    refine ⟨159199541203367079592055963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106133027468911386394703975 159199541203367079592055963)
    ·
      refine ⟨238799311805050619388083945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159199541203367079592055963 238799311805050619388083945)
      ·
        refine ⟨179099483853787964541062959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238799311805050619388083945 179099483853787964541062959)
        ·
          refine ⟨268649225780681946811594439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179099483853787964541062959 268649225780681946811594439)
          ·
            refine ⟨402973838671022920217391659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268649225780681946811594439 402973838671022920217391659)
            ·
              refine ⟨604460758006534380326087489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402973838671022920217391659 604460758006534380326087489)
              ·
                refine ⟨453345568504900785244565617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604460758006534380326087489 453345568504900785244565617)
                ·
                  refine ⟨340009176378675588933424213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453345568504900785244565617 340009176378675588933424213)
                  ·
                    refine ⟨3984482535687604557813565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 340009176378675588933424213 3984482535687604557813565)
                    ·
                      refine ⟨1494180950882851709180087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984482535687604557813565 1494180950882851709180087)
                      ·
                        rfl

theorem cell23_2909907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_2909907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909907 prefixEnd_2909907 := by exact prefixLift 2909907
  have htrace : WordTrace (prefixWord ++ tailWord_2909907) baseStart_2909907 baseEnd_2909907 := by
    simpa [prefixWord, tailWord_2909907, baseEnd_2909907] using wordTrace_append hprefix tailTrace_2909907
  have hstable : (prefixWord ++ tailWord_2909907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909907).length < 2 ^ (prefixWord ++ tailWord_2909907).sum := by decide
  have hdescent : baseEnd_2909907 < baseStart_2909907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909914 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_2909914 : Nat := 118140960795 + 2909914 * 2 ^ 59
def prefixEnd_2909914 : Nat := 4983230072969 + 3 ^ 40 * 2909914 * 2
def baseEnd_2909914 : Nat := 498061515082477727264185

theorem tailTrace_2909914 : CollatzResearch.WordTrace tailWord_2909914 prefixEnd_2909914 498061515082477727264185 := by
  unfold tailWord_2909914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533320694971506647552199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70755521853257351060139197 26533320694971506647552199)
  ·
    refine ⟨39799981042457259971328299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26533320694971506647552199 39799981042457259971328299)
    ·
      refine ⟨59699971563685889956992449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39799981042457259971328299 59699971563685889956992449)
      ·
        refine ⟨44774978672764417467744337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59699971563685889956992449 44774978672764417467744337)
        ·
          refine ⟨33581234004573313100808253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44774978672764417467744337 33581234004573313100808253)
          ·
            refine ⟨12592962751714992412803095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33581234004573313100808253 12592962751714992412803095)
            ·
              refine ⟨18889444127572488619204643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12592962751714992412803095 18889444127572488619204643)
              ·
                refine ⟨28334166191358732928806965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18889444127572488619204643 28334166191358732928806965)
                ·
                  refine ⟨2656328080439881212075653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28334166191358732928806965 2656328080439881212075653)
                  ·
                    refine ⟨498061515082477727264185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656328080439881212075653 498061515082477727264185)
                    ·
                      rfl

theorem cell23_2909914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_2909914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909914 prefixEnd_2909914 := by exact prefixLift 2909914
  have htrace : WordTrace (prefixWord ++ tailWord_2909914) baseStart_2909914 baseEnd_2909914 := by
    simpa [prefixWord, tailWord_2909914, baseEnd_2909914] using wordTrace_append hprefix tailTrace_2909914
  have hstable : (prefixWord ++ tailWord_2909914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909914).length < 2 ^ (prefixWord ++ tailWord_2909914).sum := by decide
  have hdescent : baseEnd_2909914 < baseStart_2909914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909924 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_2909924 : Nat := 118140960795 + 2909924 * 2 ^ 59
def prefixEnd_2909924 : Nat := 4983230072969 + 3 ^ 40 * 2909924 * 2
def baseEnd_2909924 : Nat := 1494189680053978142667509

theorem tailTrace_2909924 : CollatzResearch.WordTrace tailWord_2909924 prefixEnd_2909924 1494189680053978142667509 := by
  unfold tailWord_2909924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53066823754924899149036413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70755765006566532198715217 53066823754924899149036413)
  ·
    refine ⟨19900058908096837180888655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53066823754924899149036413 19900058908096837180888655)
    ·
      refine ⟨29850088362145255771332983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19900058908096837180888655 29850088362145255771332983)
      ·
        refine ⟨44775132543217883656999475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29850088362145255771332983 44775132543217883656999475)
        ·
          refine ⟨67162698814826825485499213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44775132543217883656999475 67162698814826825485499213)
          ·
            refine ⟨25186012055560059557062205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67162698814826825485499213 25186012055560059557062205)
            ·
              refine ⟨9444754520835022333898327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25186012055560059557062205 9444754520835022333898327)
              ·
                refine ⟨14167131781252533500847491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444754520835022333898327 14167131781252533500847491)
                ·
                  refine ⟨21250697671878800251271237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14167131781252533500847491 21250697671878800251271237)
                  ·
                    refine ⟨3984505813477275047113357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21250697671878800251271237 3984505813477275047113357)
                    ·
                      refine ⟨1494189680053978142667509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984505813477275047113357 1494189680053978142667509)
                      ·
                        rfl

theorem cell23_2909924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_2909924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909924 prefixEnd_2909924 := by exact prefixLift 2909924
  have htrace : WordTrace (prefixWord ++ tailWord_2909924) baseStart_2909924 baseEnd_2909924 := by
    simpa [prefixWord, tailWord_2909924, baseEnd_2909924] using wordTrace_append hprefix tailTrace_2909924
  have hstable : (prefixWord ++ tailWord_2909924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909924).length < 2 ^ (prefixWord ++ tailWord_2909924).sum := by decide
  have hdescent : baseEnd_2909924 < baseStart_2909924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909931 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 1, 4]
def baseStart_2909931 : Nat := 118140960795 + 2909931 * 2 ^ 59
def prefixEnd_2909931 : Nat := 4983230072969 + 3 ^ 40 * 2909931 * 2
def baseEnd_2909931 : Nat := 498064424806186538426659

theorem tailTrace_2909931 : CollatzResearch.WordTrace tailWord_2909931 prefixEnd_2909931 498064424806186538426659 := by
  unfold tailWord_2909931
  simp only [CollatzResearch.WordTrace]
  refine ⟨106133902820824438493577647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70755935213882958995718431 106133902820824438493577647)
  ·
    refine ⟨159200854231236657740366471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106133902820824438493577647 159200854231236657740366471)
    ·
      refine ⟨238801281346854986610549707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159200854231236657740366471 238801281346854986610549707)
      ·
        refine ⟨358201922020282479915824561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238801281346854986610549707 358201922020282479915824561)
        ·
          refine ⟨268651441515211859936868421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358201922020282479915824561 268651441515211859936868421)
          ·
            refine ⟨50372145284102223738162829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268651441515211859936868421 50372145284102223738162829)
            ·
              refine ⟨18889554481538333901811061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50372145284102223738162829 18889554481538333901811061)
              ·
                refine ⟨1770895732644218803294787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18889554481538333901811061 1770895732644218803294787)
                ·
                  refine ⟨2656343598966328204942181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770895732644218803294787 2656343598966328204942181)
                  ·
                    refine ⟨498064424806186538426659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656343598966328204942181 498064424806186538426659)
                    ·
                      rfl

theorem cell23_2909931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 4].length) (baseStart_2909931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2909931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2909931 prefixEnd_2909931 := by exact prefixLift 2909931
  have htrace : WordTrace (prefixWord ++ tailWord_2909931) baseStart_2909931 baseEnd_2909931 := by
    simpa [prefixWord, tailWord_2909931, baseEnd_2909931] using wordTrace_append hprefix tailTrace_2909931
  have hstable : (prefixWord ++ tailWord_2909931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909931).length < 2 ^ (prefixWord ++ tailWord_2909931).sum := by decide
  have hdescent : baseEnd_2909931 < baseStart_2909931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910005 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2910005 : Nat := 118140960795 + 2910005 * 2 ^ 59
def prefixEnd_2910005 : Nat := 4983230072969 + 3 ^ 40 * 2910005 * 2
def baseEnd_2910005 : Nat := 1494231271986992325754637

theorem tailTrace_2910005 : CollatzResearch.WordTrace tailWord_2910005 prefixEnd_2910005 1494231271986992325754637 := by
  unfold tailWord_2910005
  simp only [CollatzResearch.WordTrace]
  refine ⟨106136601822556349131771469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70757734548370899421180979 106136601822556349131771469)
  ·
    refine ⟨39801225683458630924414301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106136601822556349131771469 39801225683458630924414301)
    ·
      refine ⟨14925459631296986596655363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39801225683458630924414301 14925459631296986596655363)
      ·
        refine ⟨22388189446945479894983045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14925459631296986596655363 22388189446945479894983045)
        ·
          refine ⟨4197785521302277480309321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22388189446945479894983045 4197785521302277480309321)
          ·
            refine ⟨3148339140976708110231991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4197785521302277480309321 3148339140976708110231991)
            ·
              refine ⟨4722508711465062165347987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148339140976708110231991 4722508711465062165347987)
              ·
                refine ⟨7083763067197593248021981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722508711465062165347987 7083763067197593248021981)
                ·
                  refine ⟨2656411150199097468008243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7083763067197593248021981 2656411150199097468008243)
                  ·
                    refine ⟨3984616725298646202012365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2656411150199097468008243 3984616725298646202012365)
                    ·
                      refine ⟨1494231271986992325754637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984616725298646202012365 1494231271986992325754637)
                      ·
                        rfl

theorem cell23_2910005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2910005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910005 prefixEnd_2910005 := by exact prefixLift 2910005
  have htrace : WordTrace (prefixWord ++ tailWord_2910005) baseStart_2910005 baseEnd_2910005 := by
    simpa [prefixWord, tailWord_2910005, baseEnd_2910005] using wordTrace_append hprefix tailTrace_2910005
  have hstable : (prefixWord ++ tailWord_2910005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910005).length < 2 ^ (prefixWord ++ tailWord_2910005).sum := by decide
  have hdescent : baseEnd_2910005 < baseStart_2910005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910021 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2910021 : Nat := 118140960795 + 2910021 * 2 ^ 59
def prefixEnd_2910021 : Nat := 4983230072969 + 3 ^ 40 * 2910021 * 2
def baseEnd_2910021 : Nat := 498079829225821421051521

theorem tailTrace_2910021 : CollatzResearch.WordTrace tailWord_2910021 prefixEnd_2910021 498079829225821421051521 := by
  unfold tailWord_2910021
  simp only [CollatzResearch.WordTrace]
  refine ⟨106137185390498383864353917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70758123593665589242902611 106137185390498383864353917)
  ·
    refine ⟨39801444521436893949132719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106137185390498383864353917 39801444521436893949132719)
    ·
      refine ⟨59702166782155340923699079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39801444521436893949132719 59702166782155340923699079)
      ·
        refine ⟨89553250173233011385548619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59702166782155340923699079 89553250173233011385548619)
        ·
          refine ⟨134329875259849517078322929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89553250173233011385548619 134329875259849517078322929)
          ·
            refine ⟨100747406444887137808742197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134329875259849517078322929 100747406444887137808742197)
            ·
              refine ⟨9445069354208169169569581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100747406444887137808742197 9445069354208169169569581)
              ·
                refine ⟨3541901007828063438588593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9445069354208169169569581 3541901007828063438588593)
                ·
                  refine ⟨2656425755871047578941445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3541901007828063438588593 2656425755871047578941445)
                  ·
                    refine ⟨498079829225821421051521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656425755871047578941445 498079829225821421051521)
                    ·
                      rfl

theorem cell23_2910021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2910021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910021 prefixEnd_2910021 := by exact prefixLift 2910021
  have htrace : WordTrace (prefixWord ++ tailWord_2910021) baseStart_2910021 baseEnd_2910021 := by
    simpa [prefixWord, tailWord_2910021, baseEnd_2910021] using wordTrace_append hprefix tailTrace_2910021
  have hstable : (prefixWord ++ tailWord_2910021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910021).length < 2 ^ (prefixWord ++ tailWord_2910021).sum := by decide
  have hdescent : baseEnd_2910021 < baseStart_2910021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910024 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2910024 : Nat := 118140960795 + 2910024 * 2 ^ 59
def prefixEnd_2910024 : Nat := 4983230072969 + 3 ^ 40 * 2910024 * 2
def baseEnd_2910024 : Nat := 1494241028119427751417049

theorem tailTrace_2910024 : CollatzResearch.WordTrace tailWord_2910024 prefixEnd_2910024 1494241028119427751417049 := by
  unfold tailWord_2910024
  simp only [CollatzResearch.WordTrace]
  refine ⟨53068647404743757688356563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70758196539658343584475417 53068647404743757688356563)
  ·
    refine ⟨79602971107115636532534845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53068647404743757688356563 79602971107115636532534845)
    ·
      refine ⟨29851114165168363699700567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79602971107115636532534845 29851114165168363699700567)
      ·
        refine ⟨44776671247752545549550851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29851114165168363699700567 44776671247752545549550851)
        ·
          refine ⟨67165006871628818324326277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44776671247752545549550851 67165006871628818324326277)
          ·
            refine ⟨12593438788430403435811177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67165006871628818324326277 12593438788430403435811177)
            ·
              refine ⟨9445079091322802576858383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593438788430403435811177 9445079091322802576858383)
              ·
                refine ⟨14167618636984203865287575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445079091322802576858383 14167618636984203865287575)
                ·
                  refine ⟨21251427955476305797931363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14167618636984203865287575 21251427955476305797931363)
                  ·
                    refine ⟨31877141933214458696897045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21251427955476305797931363 31877141933214458696897045)
                    ·
                      refine ⟨1494241028119427751417049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31877141933214458696897045 1494241028119427751417049)
                      ·
                        rfl

theorem cell23_2910024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2910024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910024 prefixEnd_2910024 := by exact prefixLift 2910024
  have htrace : WordTrace (prefixWord ++ tailWord_2910024) baseStart_2910024 baseEnd_2910024 := by
    simpa [prefixWord, tailWord_2910024, baseEnd_2910024] using wordTrace_append hprefix tailTrace_2910024
  have hstable : (prefixWord ++ tailWord_2910024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910024).length < 2 ^ (prefixWord ++ tailWord_2910024).sum := by decide
  have hdescent : baseEnd_2910024 < baseStart_2910024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910034 : List Nat := [3, 2, 2, 1, 1, 3, 2, 9]
def baseStart_2910034 : Nat := 118140960795 + 2910034 * 2 ^ 59
def prefixEnd_2910034 : Nat := 4983230072969 + 3 ^ 40 * 2910034 * 2
def baseEnd_2910034 : Nat := 55342450478739730084889

theorem tailTrace_2910034 : CollatzResearch.WordTrace tailWord_2910034 prefixEnd_2910034 55342450478739730084889 := by
  unfold tailWord_2910034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26534414884862821771144289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70758439692967524723051437 26534414884862821771144289)
  ·
    refine ⟨19900811163647116328358217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26534414884862821771144289 19900811163647116328358217)
    ·
      refine ⟨14925608372735337246268663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19900811163647116328358217 14925608372735337246268663)
      ·
        refine ⟨22388412559103005869402995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14925608372735337246268663 22388412559103005869402995)
        ·
          refine ⟨33582618838654508804104493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22388412559103005869402995 33582618838654508804104493)
          ·
            refine ⟨12593482064495440801539185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33582618838654508804104493 12593482064495440801539185)
            ·
              refine ⟨9445111548371580601154389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593482064495440801539185 9445111548371580601154389)
              ·
                refine ⟨55342450478739730084889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9445111548371580601154389 55342450478739730084889)
                ·
                  rfl

theorem cell23_2910034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_2910034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910034 prefixEnd_2910034 := by exact prefixLift 2910034
  have htrace : WordTrace (prefixWord ++ tailWord_2910034) baseStart_2910034 baseEnd_2910034 := by
    simpa [prefixWord, tailWord_2910034, baseEnd_2910034] using wordTrace_append hprefix tailTrace_2910034
  have hstable : (prefixWord ++ tailWord_2910034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910034).length < 2 ^ (prefixWord ++ tailWord_2910034).sum := by decide
  have hdescent : baseEnd_2910034 < baseStart_2910034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910105 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 1, 3, 2]
def baseStart_2910105 : Nat := 118140960795 + 2910105 * 2 ^ 59
def prefixEnd_2910105 : Nat := 4983230072969 + 3 ^ 40 * 2910105 * 2
def baseEnd_2910105 : Nat := 1494282620052441934504177

theorem tailTrace_2910105 : CollatzResearch.WordTrace tailWord_2910105 prefixEnd_2910105 1494282620052441934504177 := by
  unfold tailWord_2910105
  simp only [CollatzResearch.WordTrace]
  refine ⟨106140249122194066210411769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70760166081462710806941179 106140249122194066210411769)
  ·
    refine ⟨79605186841645549657808827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106140249122194066210411769 79605186841645549657808827)
    ·
      refine ⟨119407780262468324486713241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79605186841645549657808827 119407780262468324486713241)
      ·
        refine ⟨89555835196851243365034931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119407780262468324486713241 89555835196851243365034931)
        ·
          refine ⟨134333752795276865047552397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89555835196851243365034931 134333752795276865047552397)
          ·
            refine ⟨50375157298228824392832149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134333752795276865047552397 50375157298228824392832149)
            ·
              refine ⟨2361335498354476143414007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50375157298228824392832149 2361335498354476143414007)
              ·
                refine ⟨3542003247531714215121011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361335498354476143414007 3542003247531714215121011)
                ·
                  refine ⟨5313004871297571322681517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542003247531714215121011 5313004871297571322681517)
                  ·
                    refine ⟨1992376826736589246005569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5313004871297571322681517 1992376826736589246005569)
                    ·
                      refine ⟨1494282620052441934504177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992376826736589246005569 1494282620052441934504177)
                      ·
                        rfl

theorem cell23_2910105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_2910105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910105 prefixEnd_2910105 := by exact prefixLift 2910105
  have htrace : WordTrace (prefixWord ++ tailWord_2910105) baseStart_2910105 baseEnd_2910105 := by
    simpa [prefixWord, tailWord_2910105, baseEnd_2910105] using wordTrace_append hprefix tailTrace_2910105
  have hstable : (prefixWord ++ tailWord_2910105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910105).length < 2 ^ (prefixWord ++ tailWord_2910105).sum := by decide
  have hdescent : baseEnd_2910105 < baseStart_2910105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910141 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 7]
def baseStart_2910141 : Nat := 118140960795 + 2910141 * 2 ^ 59
def prefixEnd_2910141 : Nat := 4983230072969 + 3 ^ 40 * 2910141 * 2
def baseEnd_2910141 : Nat := 166033456150667088183779

theorem tailTrace_2910141 : CollatzResearch.WordTrace tailWord_2910141 prefixEnd_2910141 166033456150667088183779 := by
  unfold tailWord_2910141
  simp only [CollatzResearch.WordTrace]
  refine ⟨106141562150063644358722277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70761041433375762905814851 106141562150063644358722277)
  ·
    refine ⟨19901542903136933317260427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106141562150063644358722277 19901542903136933317260427)
    ·
      refine ⟨29852314354705399975890641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19901542903136933317260427 29852314354705399975890641)
      ·
        refine ⟨22389235766029049981917981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29852314354705399975890641 22389235766029049981917981)
        ·
          refine ⟨8395963412260893743219243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22389235766029049981917981 8395963412260893743219243)
          ·
            refine ⟨12593945118391340614828865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395963412260893743219243 12593945118391340614828865)
            ·
              refine ⟨9445458838793505461121649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593945118391340614828865 9445458838793505461121649)
              ·
                refine ⟨7084094129095129095841237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9445458838793505461121649 7084094129095129095841237)
                ·
                  refine ⟨166033456150667088183779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7084094129095129095841237 166033456150667088183779)
                  ·
                    rfl

theorem cell23_2910141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_2910141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910141 prefixEnd_2910141 := by exact prefixLift 2910141
  have htrace : WordTrace (prefixWord ++ tailWord_2910141) baseStart_2910141 baseEnd_2910141 := by
    simpa [prefixWord, tailWord_2910141, baseEnd_2910141] using wordTrace_append hprefix tailTrace_2910141
  have hstable : (prefixWord ++ tailWord_2910141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910141).length < 2 ^ (prefixWord ++ tailWord_2910141).sum := by decide
  have hdescent : baseEnd_2910141 < baseStart_2910141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910175 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 5]
def baseStart_2910175 : Nat := 118140960795 + 2910175 * 2 ^ 59
def prefixEnd_2910175 : Nat := 4983230072969 + 3 ^ 40 * 2910175 * 2
def baseEnd_2910175 : Nat := 166035395966472962292095

theorem tailTrace_2910175 : CollatzResearch.WordTrace tailWord_2910175 prefixEnd_2910175 166035395966472962292095 := by
  unfold tailWord_2910175
  simp only [CollatzResearch.WordTrace]
  refine ⟨106142802231940468165459979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70761868154626978776973319 106142802231940468165459979)
  ·
    refine ⟨159214203347910702248189969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106142802231940468165459979 159214203347910702248189969)
    ·
      refine ⟨119410652510933026686142477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159214203347910702248189969 119410652510933026686142477)
      ·
        refine ⟨44778994691599885007303429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119410652510933026686142477 44778994691599885007303429)
        ·
          refine ⟨8396061504674978438869393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44778994691599885007303429 8396061504674978438869393)
          ·
            refine ⟨6297046128506233829152045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8396061504674978438869393 6297046128506233829152045)
            ·
              refine ⟨2361392298189837685932017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6297046128506233829152045 2361392298189837685932017)
              ·
                refine ⟨1771044223642378264449013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361392298189837685932017 1771044223642378264449013)
                ·
                  refine ⟨166035395966472962292095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1771044223642378264449013 166035395966472962292095)
                  ·
                    rfl

theorem cell23_2910175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 5].length) (baseStart_2910175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910175 prefixEnd_2910175 := by exact prefixLift 2910175
  have htrace : WordTrace (prefixWord ++ tailWord_2910175) baseStart_2910175 baseEnd_2910175 := by
    simpa [prefixWord, tailWord_2910175, baseEnd_2910175] using wordTrace_append hprefix tailTrace_2910175
  have hstable : (prefixWord ++ tailWord_2910175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910175).length < 2 ^ (prefixWord ++ tailWord_2910175).sum := by decide
  have hdescent : baseEnd_2910175 < baseStart_2910175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910191 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_2910191 : Nat := 118140960795 + 2910191 * 2 ^ 59
def prefixEnd_2910191 : Nat := 4983230072969 + 3 ^ 40 * 2910191 * 2
def baseEnd_2910191 : Nat := 1494326779388728598028781

theorem tailTrace_2910191 : CollatzResearch.WordTrace tailWord_2910191 prefixEnd_2910191 1494326779388728598028781 := by
  unfold tailWord_2910191
  simp only [CollatzResearch.WordTrace]
  refine ⟨106143385799882502898042427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70762257199921668598694951 106143385799882502898042427)
  ·
    refine ⟨159215078699823754347063641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106143385799882502898042427 159215078699823754347063641)
    ·
      refine ⟨119411309024867815760297731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159215078699823754347063641 119411309024867815760297731)
      ·
        refine ⟨179116963537301723640446597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119411309024867815760297731 179116963537301723640446597)
        ·
          refine ⟨33584430663244073182583737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179116963537301723640446597 33584430663244073182583737)
          ·
            refine ⟨25188322997433054886937803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33584430663244073182583737 25188322997433054886937803)
            ·
              refine ⟨37782484496149582330406705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25188322997433054886937803 37782484496149582330406705)
              ·
                refine ⟨28336863372112186747805029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37782484496149582330406705 28336863372112186747805029)
                ·
                  refine ⟨5313161882271035015213443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28336863372112186747805029 5313161882271035015213443)
                  ·
                    refine ⟨7969742823406552522820165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313161882271035015213443 7969742823406552522820165)
                    ·
                      refine ⟨1494326779388728598028781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7969742823406552522820165 1494326779388728598028781)
                      ·
                        rfl

theorem cell23_2910191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_2910191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910191 prefixEnd_2910191 := by exact prefixLift 2910191
  have htrace : WordTrace (prefixWord ++ tailWord_2910191) baseStart_2910191 baseEnd_2910191 := by
    simpa [prefixWord, tailWord_2910191, baseEnd_2910191] using wordTrace_append hprefix tailTrace_2910191
  have hstable : (prefixWord ++ tailWord_2910191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910191).length < 2 ^ (prefixWord ++ tailWord_2910191).sum := by decide
  have hdescent : baseEnd_2910191 < baseStart_2910191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910211 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3]
def baseStart_2910211 : Nat := 118140960795 + 2910211 * 2 ^ 59
def prefixEnd_2910211 : Nat := 4983230072969 + 3 ^ 40 * 2910211 * 2
def baseEnd_2910211 : Nat := 1494337049001818519778689

theorem tailTrace_2910211 : CollatzResearch.WordTrace tailWord_2910211 prefixEnd_2910211 1494337049001818519778689 := by
  unfold tailWord_2910211
  simp only [CollatzResearch.WordTrace]
  refine ⟨106144115259810046313770487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70762743506540030875846991 106144115259810046313770487)
  ·
    refine ⟨159216172889715069470655731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106144115259810046313770487 159216172889715069470655731)
    ·
      refine ⟨238824259334572604205983597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159216172889715069470655731 238824259334572604205983597)
      ·
        refine ⟨89559097250464726577243849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238824259334572604205983597 89559097250464726577243849)
        ·
          refine ⟨67169322937848544932932887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89559097250464726577243849 67169322937848544932932887)
          ·
            refine ⟨100753984406772817399399331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67169322937848544932932887 100753984406772817399399331)
            ·
              refine ⟨151130976610159226099098997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100753984406772817399399331 151130976610159226099098997)
              ·
                refine ⟨14168529057202427446790531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151130976610159226099098997 14168529057202427446790531)
                ·
                  refine ⟨21252793585803641170185797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14168529057202427446790531 21252793585803641170185797)
                  ·
                    refine ⟨3984898797338182719409837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21252793585803641170185797 3984898797338182719409837)
                    ·
                      refine ⟨1494337049001818519778689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3984898797338182719409837 1494337049001818519778689)
                      ·
                        rfl

theorem cell23_2910211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_2910211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910211 prefixEnd_2910211 := by exact prefixLift 2910211
  have htrace : WordTrace (prefixWord ++ tailWord_2910211) baseStart_2910211 baseEnd_2910211 := by
    simpa [prefixWord, tailWord_2910211, baseEnd_2910211] using wordTrace_append hprefix tailTrace_2910211
  have hstable : (prefixWord ++ tailWord_2910211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910211).length < 2 ^ (prefixWord ++ tailWord_2910211).sum := by decide
  have hdescent : baseEnd_2910211 < baseStart_2910211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910308 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2910308 : Nat := 118140960795 + 2910308 * 2 ^ 59
def prefixEnd_2910308 : Nat := 4983230072969 + 3 ^ 40 * 2910308 * 2
def baseEnd_2910308 : Nat := 498128952208434880088581

theorem tailTrace_2910308 : CollatzResearch.WordTrace tailWord_2910308 prefixEnd_2910308 498128952208434880088581 := by
  unfold tailWord_2910308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53073826570229315940025789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70765102093639087920034385 53073826570229315940025789)
  ·
    refine ⟨19902684963835993477509671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53073826570229315940025789 19902684963835993477509671)
    ·
      refine ⟨29854027445753990216264507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19902684963835993477509671 29854027445753990216264507)
      ·
        refine ⟨44781041168630985324396761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29854027445753990216264507 44781041168630985324396761)
        ·
          refine ⟨33585780876473238993297571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44781041168630985324396761 33585780876473238993297571)
          ·
            refine ⟨50378671314709858489946357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33585780876473238993297571 50378671314709858489946357)
            ·
              refine ⟨4723000435754049233432471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50378671314709858489946357 4723000435754049233432471)
              ·
                refine ⟨7084500653631073850148707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723000435754049233432471 7084500653631073850148707)
                ·
                  refine ⟨10626750980446610775223061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7084500653631073850148707 10626750980446610775223061)
                  ·
                    refine ⟨498128952208434880088581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10626750980446610775223061 498128952208434880088581)
                    ·
                      rfl

theorem cell23_2910308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2910308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910308 prefixEnd_2910308 := by exact prefixLift 2910308
  have htrace : WordTrace (prefixWord ++ tailWord_2910308) baseStart_2910308 baseEnd_2910308 := by
    simpa [prefixWord, tailWord_2910308, baseEnd_2910308] using wordTrace_append hprefix tailTrace_2910308
  have hstable : (prefixWord ++ tailWord_2910308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910308).length < 2 ^ (prefixWord ++ tailWord_2910308).sum := by decide
  have hdescent : baseEnd_2910308 < baseStart_2910308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910318 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2910318 : Nat := 118140960795 + 2910318 * 2 ^ 59
def prefixEnd_2910318 : Nat := 4983230072969 + 3 ^ 40 * 2910318 * 2
def baseEnd_2910318 : Nat := 1494391991431849601140697

theorem tailTrace_2910318 : CollatzResearch.WordTrace tailWord_2910318 prefixEnd_2910318 1494391991431849601140697 := by
  unfold tailWord_2910318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268502233802800448489451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70765345246948269058610405 13268502233802800448489451)
  ·
    refine ⟨19902753350704200672734177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13268502233802800448489451 19902753350704200672734177)
    ·
      refine ⟨14927065013028150504550633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19902753350704200672734177 14927065013028150504550633)
      ·
        refine ⟨11195298759771112878412975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14927065013028150504550633 11195298759771112878412975)
        ·
          refine ⟨16792948139656669317619463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195298759771112878412975 16792948139656669317619463)
          ·
            refine ⟨25189422209485003976429195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16792948139656669317619463 25189422209485003976429195)
            ·
              refine ⟨37784133314227505964643793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25189422209485003976429195 37784133314227505964643793)
              ·
                refine ⟨28338099985670629473482845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37784133314227505964643793 28338099985670629473482845)
                ·
                  refine ⟨10626787494626486052556067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28338099985670629473482845 10626787494626486052556067)
                  ·
                    refine ⟨15940181241939729078834101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10626787494626486052556067 15940181241939729078834101)
                    ·
                      refine ⟨1494391991431849601140697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15940181241939729078834101 1494391991431849601140697)
                      ·
                        rfl

theorem cell23_2910318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2910318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910318 prefixEnd_2910318 := by exact prefixLift 2910318
  have htrace : WordTrace (prefixWord ++ tailWord_2910318) baseStart_2910318 baseEnd_2910318 := by
    simpa [prefixWord, tailWord_2910318, baseEnd_2910318] using wordTrace_append hprefix tailTrace_2910318
  have hstable : (prefixWord ++ tailWord_2910318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910318).length < 2 ^ (prefixWord ++ tailWord_2910318).sum := by decide
  have hdescent : baseEnd_2910318 < baseStart_2910318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910321 : List Nat := [1, 2, 2, 2, 1, 1, 5, 9]
def baseStart_2910321 : Nat := 118140960795 + 2910321 * 2 ^ 59
def prefixEnd_2910321 : Nat := 4983230072969 + 3 ^ 40 * 2910321 * 2
def baseEnd_2910321 : Nat := 55347908587919003311229

theorem tailTrace_2910321 : CollatzResearch.WordTrace tailWord_2910321 prefixEnd_2910321 55347908587919003311229 := by
  unfold tailWord_2910321
  simp only [CollatzResearch.WordTrace]
  refine ⟨106148127289411535100274817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70765418192941023400183211 106148127289411535100274817)
  ·
    refine ⟨79611095467058651325206113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106148127289411535100274817 79611095467058651325206113)
    ·
      refine ⟨59708321600293988493904585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79611095467058651325206113 59708321600293988493904585)
      ·
        refine ⟨44781241200220491370428439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59708321600293988493904585 44781241200220491370428439)
        ·
          refine ⟨67171861800330737055642659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44781241200220491370428439 67171861800330737055642659)
          ·
            refine ⟨100757792700496105583463989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67171861800330737055642659 100757792700496105583463989)
            ·
              refine ⟨9446043065671509898449749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100757792700496105583463989 9446043065671509898449749)
              ·
                refine ⟨55347908587919003311229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9446043065671509898449749 55347908587919003311229)
                ·
                  rfl

theorem cell23_2910321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 9].length) (baseStart_2910321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910321 prefixEnd_2910321 := by exact prefixLift 2910321
  have htrace : WordTrace (prefixWord ++ tailWord_2910321) baseStart_2910321 baseEnd_2910321 := by
    simpa [prefixWord, tailWord_2910321, baseEnd_2910321] using wordTrace_append hprefix tailTrace_2910321
  have hstable : (prefixWord ++ tailWord_2910321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910321).length < 2 ^ (prefixWord ++ tailWord_2910321).sum := by decide
  have hdescent : baseEnd_2910321 < baseStart_2910321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910326 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2910326 : Nat := 118140960795 + 2910326 * 2 ^ 59
def prefixEnd_2910326 : Nat := 4983230072969 + 3 ^ 40 * 2910326 * 2
def baseEnd_2910326 : Nat := 1494396099277085569840661

theorem tailTrace_2910326 : CollatzResearch.WordTrace tailWord_2910326 prefixEnd_2910326 1494396099277085569840661 := by
  unfold tailWord_2910326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634269353399588809637927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70765539769595613969471221 6634269353399588809637927)
  ·
    refine ⟨9951404030099383214456891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634269353399588809637927 9951404030099383214456891)
    ·
      refine ⟨14927106045149074821685337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951404030099383214456891 14927106045149074821685337)
      ·
        refine ⟨11195329533861806116264003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14927106045149074821685337 11195329533861806116264003)
        ·
          refine ⟨16792994300792709174396005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195329533861806116264003 16792994300792709174396005)
          ·
            refine ⟨3148686431398632970199251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16792994300792709174396005 3148686431398632970199251)
            ·
              refine ⟨4723029647097949455298877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148686431398632970199251 4723029647097949455298877)
              ·
                refine ⟨1771136117661731045737079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723029647097949455298877 1771136117661731045737079)
                ·
                  refine ⟨2656704176492596568605619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771136117661731045737079 2656704176492596568605619)
                  ·
                    refine ⟨3985056264738894852908429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2656704176492596568605619 3985056264738894852908429)
                    ·
                      refine ⟨1494396099277085569840661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3985056264738894852908429 1494396099277085569840661)
                      ·
                        rfl

theorem cell23_2910326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2910326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910326 prefixEnd_2910326 := by exact prefixLift 2910326
  have htrace : WordTrace (prefixWord ++ tailWord_2910326) baseStart_2910326 baseEnd_2910326 := by
    simpa [prefixWord, tailWord_2910326, baseEnd_2910326] using wordTrace_append hprefix tailTrace_2910326
  have hstable : (prefixWord ++ tailWord_2910326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910326).length < 2 ^ (prefixWord ++ tailWord_2910326).sum := by decide
  have hdescent : baseEnd_2910326 < baseStart_2910326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910359 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 2, 4]
def baseStart_2910359 : Nat := 118140960795 + 2910359 * 2 ^ 59
def prefixEnd_2910359 : Nat := 4983230072969 + 3 ^ 40 * 2910359 * 2
def baseEnd_2910359 : Nat := 498137681379561313576003

theorem tailTrace_2910359 : CollatzResearch.WordTrace tailWord_2910359 prefixEnd_2910359 498137681379561313576003 := by
  unfold tailWord_2910359
  simp only [CollatzResearch.WordTrace]
  refine ⟨106149513263273867590158131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70766342175515911726772087 106149513263273867590158131)
  ·
    refine ⟨159224269894910801385237197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106149513263273867590158131 159224269894910801385237197)
    ·
      refine ⟨59709101210591550519463949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159224269894910801385237197 59709101210591550519463949)
      ·
        refine ⟨22390912953971831444798981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59709101210591550519463949 22390912953971831444798981)
        ·
          refine ⟨4198296178869718395899809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22390912953971831444798981 4198296178869718395899809)
          ·
            refine ⟨3148722134152288796924857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4198296178869718395899809 3148722134152288796924857)
            ·
              refine ⟨2361541600614216597693643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148722134152288796924857 2361541600614216597693643)
              ·
                refine ⟨3542312400921324896540465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361541600614216597693643 3542312400921324896540465)
                ·
                  refine ⟨2656734300690993672405349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542312400921324896540465 2656734300690993672405349)
                  ·
                    refine ⟨498137681379561313576003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656734300690993672405349 498137681379561313576003)
                    ·
                      rfl

theorem cell23_2910359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_2910359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910359 prefixEnd_2910359 := by exact prefixLift 2910359
  have htrace : WordTrace (prefixWord ++ tailWord_2910359) baseStart_2910359 baseEnd_2910359 := by
    simpa [prefixWord, tailWord_2910359, baseEnd_2910359] using wordTrace_append hprefix tailTrace_2910359
  have hstable : (prefixWord ++ tailWord_2910359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910359).length < 2 ^ (prefixWord ++ tailWord_2910359).sum := by decide
  have hdescent : baseEnd_2910359 < baseStart_2910359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910366 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2910366 : Nat := 118140960795 + 2910366 * 2 ^ 59
def prefixEnd_2910366 : Nat := 4983230072969 + 3 ^ 40 * 2910366 * 2
def baseEnd_2910366 : Nat := 1494416638503265413340477

theorem tailTrace_2910366 : CollatzResearch.WordTrace tailWord_2910366 prefixEnd_2910366 1494416638503265413340477 := by
  unfold tailWord_2910366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268721071781063473207869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70766512382832338523775301 13268721071781063473207869)
  ·
    refine ⟨4975770401917898802452951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13268721071781063473207869 4975770401917898802452951)
    ·
      refine ⟨7463655602876848203679427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4975770401917898802452951 7463655602876848203679427)
      ·
        refine ⟨11195483404315272305519141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463655602876848203679427 11195483404315272305519141)
        ·
          refine ⟨2099153138309113557284839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11195483404315272305519141 2099153138309113557284839)
          ·
            refine ⟨3148729707463670335927259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099153138309113557284839 3148729707463670335927259)
            ·
              refine ⟨4723094561195505503890889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148729707463670335927259 4723094561195505503890889)
              ·
                refine ⟨3542320920896629127918167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4723094561195505503890889 3542320920896629127918167)
                ·
                  refine ⟨5313481381344943691877251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542320920896629127918167 5313481381344943691877251)
                  ·
                    refine ⟨7970222072017415537815877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313481381344943691877251 7970222072017415537815877)
                    ·
                      refine ⟨1494416638503265413340477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7970222072017415537815877 1494416638503265413340477)
                      ·
                        rfl

theorem cell23_2910366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2910366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910366 prefixEnd_2910366 := by exact prefixLift 2910366
  have htrace : WordTrace (prefixWord ++ tailWord_2910366) baseStart_2910366 baseEnd_2910366 := by
    simpa [prefixWord, tailWord_2910366, baseEnd_2910366] using wordTrace_append hprefix tailTrace_2910366
  have hstable : (prefixWord ++ tailWord_2910366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910366).length < 2 ^ (prefixWord ++ tailWord_2910366).sum := by decide
  have hdescent : baseEnd_2910366 < baseStart_2910366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2910371 : Nat := 118140960795 + 2910371 * 2 ^ 59
def prefixEnd_2910371 : Nat := 4983230072969 + 3 ^ 40 * 2910371 * 2
def baseEnd_2910371 : Nat := 1494419205906537893777953

theorem tailTrace_2910371 : CollatzResearch.WordTrace tailWord_2910371 prefixEnd_2910371 1494419205906537893777953 := by
  unfold tailWord_2910371
  simp only [CollatzResearch.WordTrace]
  refine ⟨106149950939230393639594967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70766633959486929093063311 106149950939230393639594967)
  ·
    refine ⟨159224926408845590459392451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106149950939230393639594967 159224926408845590459392451)
    ·
      refine ⟨238837389613268385689088677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159224926408845590459392451 238837389613268385689088677)
      ·
        refine ⟨44782010552487822316704127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238837389613268385689088677 44782010552487822316704127)
        ·
          refine ⟨67173015828731733475056191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44782010552487822316704127 67173015828731733475056191)
          ·
            refine ⟨100759523743097600212584287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67173015828731733475056191 100759523743097600212584287)
            ·
              refine ⟨151139285614646400318876431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100759523743097600212584287 151139285614646400318876431)
              ·
                refine ⟨226708928421969600478314647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151139285614646400318876431 226708928421969600478314647)
                ·
                  refine ⟨340063392632954400717471971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226708928421969600478314647 340063392632954400717471971)
                  ·
                    refine ⟨510095088949431601076207957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340063392632954400717471971 510095088949431601076207957)
                    ·
                      refine ⟨1494419205906537893777953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 510095088949431601076207957 1494419205906537893777953)
                      ·
                        rfl

theorem cell23_2910371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2910371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910371 prefixEnd_2910371 := by exact prefixLift 2910371
  have htrace : WordTrace (prefixWord ++ tailWord_2910371) baseStart_2910371 baseEnd_2910371 := by
    simpa [prefixWord, tailWord_2910371, baseEnd_2910371] using wordTrace_append hprefix tailTrace_2910371
  have hstable : (prefixWord ++ tailWord_2910371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910371).length < 2 ^ (prefixWord ++ tailWord_2910371).sum := by decide
  have hdescent : baseEnd_2910371 < baseStart_2910371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910402 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2910402 : Nat := 118140960795 + 2910402 * 2 ^ 59
def prefixEnd_2910402 : Nat := 4983230072969 + 3 ^ 40 * 2910402 * 2
def baseEnd_2910402 : Nat := 498145041268942424163437

theorem tailTrace_2910402 : CollatzResearch.WordTrace tailWord_2910402 prefixEnd_2910402 498145041268942424163437 := by
  unfold tailWord_2910402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537770400529521483493365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70767387734745390622648973 26537770400529521483493365)
  ·
    refine ⟨2487915975049642639077503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26537770400529521483493365 2487915975049642639077503)
    ·
      refine ⟨3731873962574463958616255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487915975049642639077503 3731873962574463958616255)
      ·
        refine ⟨5597810943861695937924383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731873962574463958616255 5597810943861695937924383)
        ·
          refine ⟨8396716415792543906886575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5597810943861695937924383 8396716415792543906886575)
          ·
            refine ⟨12595074623688815860329863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396716415792543906886575 12595074623688815860329863)
            ·
              refine ⟨18892611935533223790494795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12595074623688815860329863 18892611935533223790494795)
              ·
                refine ⟨28338917903299835685742193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18892611935533223790494795 28338917903299835685742193)
                ·
                  refine ⟨21254188427474876764306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28338917903299835685742193 21254188427474876764306645)
                  ·
                    refine ⟨498145041268942424163437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21254188427474876764306645 498145041268942424163437)
                    ·
                      rfl

theorem cell23_2910402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2910402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910402 prefixEnd_2910402 := by exact prefixLift 2910402
  have htrace : WordTrace (prefixWord ++ tailWord_2910402) baseStart_2910402 baseEnd_2910402 := by
    simpa [prefixWord, tailWord_2910402, baseEnd_2910402] using wordTrace_append hprefix tailTrace_2910402
  have hstable : (prefixWord ++ tailWord_2910402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910402).length < 2 ^ (prefixWord ++ tailWord_2910402).sum := by decide
  have hdescent : baseEnd_2910402 < baseStart_2910402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910462 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2910462 : Nat := 118140960795 + 2910462 * 2 ^ 59
def prefixEnd_2910462 : Nat := 4983230072969 + 3 ^ 40 * 2910462 * 2
def baseEnd_2910462 : Nat := 166051770294010781971115

theorem tailTrace_2910462 : CollatzResearch.WordTrace tailWord_2910462 prefixEnd_2910462 166051770294010781971115 := by
  unfold tailWord_2910462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269158747737589522644705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70768846654600477454105093 13269158747737589522644705)
  ·
    refine ⟨9951869060803192141983529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13269158747737589522644705 9951869060803192141983529)
    ·
      refine ⟨7463901795602394106487647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9951869060803192141983529 7463901795602394106487647)
      ·
        refine ⟨11195852693403591159731471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463901795602394106487647 11195852693403591159731471)
        ·
          refine ⟨16793779040105386739597207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195852693403591159731471 16793779040105386739597207)
          ·
            refine ⟨25190668560158080109395811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16793779040105386739597207 25190668560158080109395811)
            ·
              refine ⟨37786002840237120164093717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25190668560158080109395811 37786002840237120164093717)
              ·
                refine ⟨1771218883136115007691893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37786002840237120164093717 1771218883136115007691893)
                ·
                  refine ⟨166051770294010781971115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1771218883136115007691893 166051770294010781971115)
                  ·
                    rfl

theorem cell23_2910462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2910462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910462 prefixEnd_2910462 := by exact prefixLift 2910462
  have htrace : WordTrace (prefixWord ++ tailWord_2910462) baseStart_2910462 baseEnd_2910462 := by
    simpa [prefixWord, tailWord_2910462, baseEnd_2910462] using wordTrace_append hprefix tailTrace_2910462
  have hstable : (prefixWord ++ tailWord_2910462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910462).length < 2 ^ (prefixWord ++ tailWord_2910462).sum := by decide
  have hdescent : baseEnd_2910462 < baseStart_2910462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910488 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_2910488 : Nat := 118140960795 + 2910488 * 2 ^ 59
def prefixEnd_2910488 : Nat := 4983230072969 + 3 ^ 40 * 2910488 * 2
def baseEnd_2910488 : Nat := 498159761047704645338305

theorem tailTrace_2910488 : CollatzResearch.WordTrace tailWord_2910488 prefixEnd_2910488 498159761047704645338305 := by
  unfold tailWord_2910488
  simp only [CollatzResearch.WordTrace]
  refine ⟨53077109139903261310802059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70769478853204348414402745 53077109139903261310802059)
  ·
    refine ⟨79615663709854891966203089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53077109139903261310802059 79615663709854891966203089)
    ·
      refine ⟨59711747782391168974652317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79615663709854891966203089 59711747782391168974652317)
      ·
        refine ⟨22391905418396688365494619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59711747782391168974652317 22391905418396688365494619)
        ·
          refine ⟨33587858127595032548241929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22391905418396688365494619 33587858127595032548241929)
          ·
            refine ⟨25190893595696274411181447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33587858127595032548241929 25190893595696274411181447)
            ·
              refine ⟨37786340393544411616772171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25190893595696274411181447 37786340393544411616772171)
              ·
                refine ⟨56679510590316617425158257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37786340393544411616772171 56679510590316617425158257)
                ·
                  refine ⟨42509632942737463068868693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56679510590316617425158257 42509632942737463068868693)
                  ·
                    refine ⟨498159761047704645338305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42509632942737463068868693 498159761047704645338305)
                    ·
                      rfl

theorem cell23_2910488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_2910488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910488 prefixEnd_2910488 := by exact prefixLift 2910488
  have htrace : WordTrace (prefixWord ++ tailWord_2910488) baseStart_2910488 baseEnd_2910488 := by
    simpa [prefixWord, tailWord_2910488, baseEnd_2910488] using wordTrace_append hprefix tailTrace_2910488
  have hstable : (prefixWord ++ tailWord_2910488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910488).length < 2 ^ (prefixWord ++ tailWord_2910488).sum := by decide
  have hdescent : baseEnd_2910488 < baseStart_2910488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910495 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2910495 : Nat := 118140960795 + 2910495 * 2 ^ 59
def prefixEnd_2910495 : Nat := 4983230072969 + 3 ^ 40 * 2910495 * 2
def baseEnd_2910495 : Nat := 1494482877507695408627383

theorem tailTrace_2910495 : CollatzResearch.WordTrace tailWord_2910495 prefixEnd_2910495 1494482877507695408627383 := by
  unfold tailWord_2910495
  simp only [CollatzResearch.WordTrace]
  refine ⟨106154473590781162817108939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70769649060520775211405959 106154473590781162817108939)
  ·
    refine ⟨159231710386171744225663409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106154473590781162817108939 159231710386171744225663409)
    ·
      refine ⟨119423782789628808169247557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159231710386171744225663409 119423782789628808169247557)
      ·
        refine ⟨22391959273055401531733917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119423782789628808169247557 22391959273055401531733917)
        ·
          refine ⟨8396984727395775574400219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22391959273055401531733917 8396984727395775574400219)
          ·
            refine ⟨12595477091093663361600329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396984727395775574400219 12595477091093663361600329)
            ·
              refine ⟨9446607818320247521200247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12595477091093663361600329 9446607818320247521200247)
              ·
                refine ⟨14169911727480371281800371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9446607818320247521200247 14169911727480371281800371)
                ·
                  refine ⟨21254867591220556922700557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14169911727480371281800371 21254867591220556922700557)
                  ·
                    refine ⟨7970575346707708846012709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21254867591220556922700557 7970575346707708846012709)
                    ·
                      refine ⟨1494482877507695408627383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7970575346707708846012709 1494482877507695408627383)
                      ·
                        rfl

theorem cell23_2910495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2910495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910495 prefixEnd_2910495 := by exact prefixLift 2910495
  have htrace : WordTrace (prefixWord ++ tailWord_2910495) baseStart_2910495 baseEnd_2910495 := by
    simpa [prefixWord, tailWord_2910495, baseEnd_2910495] using wordTrace_append hprefix tailTrace_2910495
  have hstable : (prefixWord ++ tailWord_2910495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910495).length < 2 ^ (prefixWord ++ tailWord_2910495).sum := by decide
  have hdescent : baseEnd_2910495 < baseStart_2910495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910508 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2910508 : Nat := 118140960795 + 2910508 * 2 ^ 59
def prefixEnd_2910508 : Nat := 4983230072969 + 3 ^ 40 * 2910508 * 2
def baseEnd_2910508 : Nat := 1494489552756203857764823

theorem tailTrace_2910508 : CollatzResearch.WordTrace tailWord_2910508 prefixEnd_2910508 1494489552756203857764823 := by
  unfold tailWord_2910508
  simp only [CollatzResearch.WordTrace]
  refine ⟨53077473869867033018666089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70769965159822710691554785 53077473869867033018666089)
  ·
    refine ⟨39808105402400274763999567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53077473869867033018666089 39808105402400274763999567)
    ·
      refine ⟨59712158103600412145999351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39808105402400274763999567 59712158103600412145999351)
      ·
        refine ⟨89568237155400618218999027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59712158103600412145999351 89568237155400618218999027)
        ·
          refine ⟨134352355733100927328498541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89568237155400618218999027 134352355733100927328498541)
          ·
            refine ⟨50382133399912847748186953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134352355733100927328498541 50382133399912847748186953)
            ·
              refine ⟨37786600049934635811140215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50382133399912847748186953 37786600049934635811140215)
              ·
                refine ⟨56679900074901953716710323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37786600049934635811140215 56679900074901953716710323)
                ·
                  refine ⟨85019850112352930575065485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56679900074901953716710323 85019850112352930575065485)
                  ·
                    refine ⟨31882443792132348965649557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85019850112352930575065485 31882443792132348965649557)
                    ·
                      refine ⟨1494489552756203857764823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31882443792132348965649557 1494489552756203857764823)
                      ·
                        rfl

theorem cell23_2910508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2910508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910508 prefixEnd_2910508 := by exact prefixLift 2910508
  have htrace : WordTrace (prefixWord ++ tailWord_2910508) baseStart_2910508 baseEnd_2910508 := by
    simpa [prefixWord, tailWord_2910508, baseEnd_2910508] using wordTrace_append hprefix tailTrace_2910508
  have hstable : (prefixWord ++ tailWord_2910508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910508).length < 2 ^ (prefixWord ++ tailWord_2910508).sum := by decide
  have hdescent : baseEnd_2910508 < baseStart_2910508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910509 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2910509 : Nat := 118140960795 + 2910509 * 2 ^ 59
def prefixEnd_2910509 : Nat := 4983230072969 + 3 ^ 40 * 2910509 * 2
def baseEnd_2910509 : Nat := 498163355412286117950773

theorem tailTrace_2910509 : CollatzResearch.WordTrace tailWord_2910509 prefixEnd_2910509 498163355412286117950773 := by
  unfold tailWord_2910509
  simp only [CollatzResearch.WordTrace]
  refine ⟨106154984212730443208118581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70769989475153628805412387 106154984212730443208118581)
  ·
    refine ⟨9952029769943479050761117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106154984212730443208118581 9952029769943479050761117)
    ·
      refine ⟨3732011163728804644035419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9952029769943479050761117 3732011163728804644035419)
      ·
        refine ⟨5598016745593206966053129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732011163728804644035419 5598016745593206966053129)
        ·
          refine ⟨4198512559194905224539847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5598016745593206966053129 4198512559194905224539847)
          ·
            refine ⟨6297768838792357836809771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198512559194905224539847 6297768838792357836809771)
            ·
              refine ⟨9446653258188536755214657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297768838792357836809771 9446653258188536755214657)
              ·
                refine ⟨7084989943641402566410993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9446653258188536755214657 7084989943641402566410993)
                ·
                  refine ⟨5313742457731051924808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7084989943641402566410993 5313742457731051924808245)
                  ·
                    refine ⟨498163355412286117950773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5313742457731051924808245 498163355412286117950773)
                    ·
                      rfl

theorem cell23_2910509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2910509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910509 prefixEnd_2910509 := by exact prefixLift 2910509
  have htrace : WordTrace (prefixWord ++ tailWord_2910509) baseStart_2910509 baseEnd_2910509 := by
    simpa [prefixWord, tailWord_2910509, baseEnd_2910509] using wordTrace_append hprefix tailTrace_2910509
  have hstable : (prefixWord ++ tailWord_2910509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910509).length < 2 ^ (prefixWord ++ tailWord_2910509).sum := by decide
  have hdescent : baseEnd_2910509 < baseStart_2910509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910522 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_2910522 : Nat := 118140960795 + 2910522 * 2 ^ 59
def prefixEnd_2910522 : Nat := 4983230072969 + 3 ^ 40 * 2910522 * 2
def baseEnd_2910522 : Nat := 498165580495122267663253

theorem tailTrace_2910522 : CollatzResearch.WordTrace tailWord_2910522 prefixEnd_2910522 498165580495122267663253 := by
  unfold tailWord_2910522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538864590420836607085455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70770305574455564285561213 26538864590420836607085455)
  ·
    refine ⟨39808296885631254910628183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26538864590420836607085455 39808296885631254910628183)
    ·
      refine ⟨59712445328446882365942275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39808296885631254910628183 59712445328446882365942275)
      ·
        refine ⟨89568667992670323548913413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59712445328446882365942275 89568667992670323548913413)
        ·
          refine ⟨16794125248625685665421265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89568667992670323548913413 16794125248625685665421265)
          ·
            refine ⟨12595593936469264249065949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16794125248625685665421265 12595593936469264249065949)
            ·
              refine ⟨4723347726175974093399731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12595593936469264249065949 4723347726175974093399731)
              ·
                refine ⟨7085021589263961140099597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723347726175974093399731 7085021589263961140099597)
                ·
                  refine ⟨2656883095973985427537349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7085021589263961140099597 2656883095973985427537349)
                  ·
                    refine ⟨498165580495122267663253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2656883095973985427537349 498165580495122267663253)
                    ·
                      rfl

theorem cell23_2910522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_2910522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910522 prefixEnd_2910522 := by exact prefixLift 2910522
  have htrace : WordTrace (prefixWord ++ tailWord_2910522) baseStart_2910522 baseEnd_2910522 := by
    simpa [prefixWord, tailWord_2910522, baseEnd_2910522] using wordTrace_append hprefix tailTrace_2910522
  have hstable : (prefixWord ++ tailWord_2910522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910522).length < 2 ^ (prefixWord ++ tailWord_2910522).sum := by decide
  have hdescent : baseEnd_2910522 < baseStart_2910522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910535 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 6]
def baseStart_2910535 : Nat := 118140960795 + 2910535 * 2 ^ 59
def prefixEnd_2910535 : Nat := 4983230072969 + 3 ^ 40 * 2910535 * 2
def baseEnd_2910535 : Nat := 166055935192652805791911

theorem tailTrace_2910535 : CollatzResearch.WordTrace tailWord_2910535 prefixEnd_2910535 166055935192652805791911 := by
  unfold tailWord_2910535
  simp only [CollatzResearch.WordTrace]
  refine ⟨106155932510636249648565059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70770621673757499765710039 106155932510636249648565059)
  ·
    refine ⟨159233898765954374472847589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106155932510636249648565059 159233898765954374472847589)
    ·
      refine ⟨29856356018616445213658923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159233898765954374472847589 29856356018616445213658923)
      ·
        refine ⟨44784534027924667820488385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29856356018616445213658923 44784534027924667820488385)
        ·
          refine ⟨33588400520943500865366289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44784534027924667820488385 33588400520943500865366289)
          ·
            refine ⟨25191300390707625649024717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33588400520943500865366289 25191300390707625649024717)
            ·
              refine ⟨9446737646515359618384269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25191300390707625649024717 9446737646515359618384269)
              ·
                refine ⟨3542526617443259856894101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9446737646515359618384269 3542526617443259856894101)
                ·
                  refine ⟨166055935192652805791911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3542526617443259856894101 166055935192652805791911)
                  ·
                    rfl

theorem cell23_2910535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 6].length) (baseStart_2910535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910535 prefixEnd_2910535 := by exact prefixLift 2910535
  have htrace : WordTrace (prefixWord ++ tailWord_2910535) baseStart_2910535 baseEnd_2910535 := by
    simpa [prefixWord, tailWord_2910535, baseEnd_2910535] using wordTrace_append hprefix tailTrace_2910535
  have hstable : (prefixWord ++ tailWord_2910535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910535).length < 2 ^ (prefixWord ++ tailWord_2910535).sum := by decide
  have hdescent : baseEnd_2910535 < baseStart_2910535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910549 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2910549 : Nat := 118140960795 + 2910549 * 2 ^ 59
def prefixEnd_2910549 : Nat := 4983230072969 + 3 ^ 40 * 2910549 * 2
def baseEnd_2910549 : Nat := 1494510605463038197352135

theorem tailTrace_2910549 : CollatzResearch.WordTrace tailWord_2910549 prefixEnd_2910549 1494510605463038197352135 := by
  unfold tailWord_2910549
  simp only [CollatzResearch.WordTrace]
  refine ⟨106156443132585530039574701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70770962088390353359716467 106156443132585530039574701)
  ·
    refine ⟨39808666174719573764840513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106156443132585530039574701 39808666174719573764840513)
    ·
      refine ⟨29856499631039680323630385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39808666174719573764840513 29856499631039680323630385)
      ·
        refine ⟨22392374723279760242722789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29856499631039680323630385 22392374723279760242722789)
        ·
          refine ⟨4198570260614955045510523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22392374723279760242722789 4198570260614955045510523)
          ·
            refine ⟨6297855390922432568265785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198570260614955045510523 6297855390922432568265785)
            ·
              refine ⟨4723391543191824426199339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6297855390922432568265785 4723391543191824426199339)
              ·
                refine ⟨7085087314787736639299009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723391543191824426199339 7085087314787736639299009)
                ·
                  refine ⟨5313815486090802479474257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085087314787736639299009 5313815486090802479474257)
                  ·
                    refine ⟨3985361614568101859605693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313815486090802479474257 3985361614568101859605693)
                    ·
                      refine ⟨1494510605463038197352135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3985361614568101859605693 1494510605463038197352135)
                      ·
                        rfl

theorem cell23_2910549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2910549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910549 prefixEnd_2910549 := by exact prefixLift 2910549
  have htrace : WordTrace (prefixWord ++ tailWord_2910549) baseStart_2910549 baseEnd_2910549 := by
    simpa [prefixWord, tailWord_2910549, baseEnd_2910549] using wordTrace_append hprefix tailTrace_2910549
  have hstable : (prefixWord ++ tailWord_2910549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910549).length < 2 ^ (prefixWord ++ tailWord_2910549).sum := by decide
  have hdescent : baseEnd_2910549 < baseStart_2910549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 1, 1, 3]
def baseStart_2910579 : Nat := 118140960795 + 2910579 * 2 ^ 59
def prefixEnd_2910579 : Nat := 4983230072969 + 3 ^ 40 * 2910579 * 2
def baseEnd_2910579 : Nat := 1494526009882673079976997

theorem tailTrace_2910579 : CollatzResearch.WordTrace tailWord_2910579 prefixEnd_2910579 1494526009882673079976997 := by
  unfold tailWord_2910579
  simp only [CollatzResearch.WordTrace]
  refine ⟨106157537322476845163166791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70771691548317896775444527 106157537322476845163166791)
  ·
    refine ⟨159236305983715267744750187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106157537322476845163166791 159236305983715267744750187)
    ·
      refine ⟨238854458975572901617125281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159236305983715267744750187 238854458975572901617125281)
      ·
        refine ⟨179140844231679676212843961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238854458975572901617125281 179140844231679676212843961)
        ·
          refine ⟨134355633173759757159632971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179140844231679676212843961 134355633173759757159632971)
          ·
            refine ⟨201533449760639635739449457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134355633173759757159632971 201533449760639635739449457)
            ·
              refine ⟨151150087320479726804587093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201533449760639635739449457 151150087320479726804587093)
              ·
                refine ⟨1771290085786871798491255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 151150087320479726804587093 1771290085786871798491255)
                ·
                  refine ⟨2656935128680307697736883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771290085786871798491255 2656935128680307697736883)
                  ·
                    refine ⟨3985402693020461546605325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2656935128680307697736883 3985402693020461546605325)
                    ·
                      refine ⟨1494526009882673079976997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3985402693020461546605325 1494526009882673079976997)
                      ·
                        rfl

theorem cell23_2910579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 1, 3].length) (baseStart_2910579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910579 prefixEnd_2910579 := by exact prefixLift 2910579
  have htrace : WordTrace (prefixWord ++ tailWord_2910579) baseStart_2910579 baseEnd_2910579 := by
    simpa [prefixWord, tailWord_2910579, baseEnd_2910579] using wordTrace_append hprefix tailTrace_2910579
  have hstable : (prefixWord ++ tailWord_2910579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910579).length < 2 ^ (prefixWord ++ tailWord_2910579).sum := by decide
  have hdescent : baseEnd_2910579 < baseStart_2910579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910606 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2910606 : Nat := 118140960795 + 2910606 * 2 ^ 59
def prefixEnd_2910606 : Nat := 4983230072969 + 3 ^ 40 * 2910606 * 2
def baseEnd_2910606 : Nat := 1494539873860344474339373

theorem tailTrace_2910606 : CollatzResearch.WordTrace tailWord_2910606 prefixEnd_2910606 1494539873860344474339373 := by
  unfold tailWord_2910606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269815261672378596799959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70772348062252685849599781 13269815261672378596799959)
  ·
    refine ⟨19904722892508567895199939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13269815261672378596799959 19904722892508567895199939)
    ·
      refine ⟨29857084338762851842799909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19904722892508567895199939 29857084338762851842799909)
      ·
        refine ⟨5598203313518034720524983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29857084338762851842799909 5598203313518034720524983)
        ·
          refine ⟨8397304970277052080787475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598203313518034720524983 8397304970277052080787475)
          ·
            refine ⟨12595957455415578121181213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8397304970277052080787475 12595957455415578121181213)
            ·
              refine ⟨4723484045780841795442955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12595957455415578121181213 4723484045780841795442955)
              ·
                refine ⟨7085226068671262693164433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723484045780841795442955 7085226068671262693164433)
                ·
                  refine ⟨5313919551503447019873325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085226068671262693164433 5313919551503447019873325)
                  ·
                    refine ⟨1992719831813792632452497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5313919551503447019873325 1992719831813792632452497)
                    ·
                      refine ⟨1494539873860344474339373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992719831813792632452497 1494539873860344474339373)
                      ·
                        rfl

theorem cell23_2910606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2910606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910606 prefixEnd_2910606 := by exact prefixLift 2910606
  have htrace : WordTrace (prefixWord ++ tailWord_2910606) baseStart_2910606 baseEnd_2910606 := by
    simpa [prefixWord, tailWord_2910606, baseEnd_2910606] using wordTrace_append hprefix tailTrace_2910606
  have hstable : (prefixWord ++ tailWord_2910606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910606).length < 2 ^ (prefixWord ++ tailWord_2910606).sum := by decide
  have hdescent : baseEnd_2910606 < baseStart_2910606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910616 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_2910616 : Nat := 118140960795 + 2910616 * 2 ^ 59
def prefixEnd_2910616 : Nat := 4983230072969 + 3 ^ 40 * 2910616 * 2
def baseEnd_2910616 : Nat := 498181669555629811738109

theorem tailTrace_2910616 : CollatzResearch.WordTrace tailWord_2910616 prefixEnd_2910616 498181669555629811738109 := by
  unfold tailWord_2910616
  simp only [CollatzResearch.WordTrace]
  refine ⟨53079443411671400241131851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70772591215561866988175801 53079443411671400241131851)
  ·
    refine ⟨79619165117507100361697777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53079443411671400241131851 79619165117507100361697777)
    ·
      refine ⟨59714373838130325271273333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79619165117507100361697777 59714373838130325271273333)
      ·
        refine ⟨5598222547324717994181875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59714373838130325271273333 5598222547324717994181875)
        ·
          refine ⟨8397333820987076991272813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598222547324717994181875 8397333820987076991272813)
          ·
            refine ⟨3149000182870153871727305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8397333820987076991272813 3149000182870153871727305)
            ·
              refine ⟨2361750137152615403795479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149000182870153871727305 2361750137152615403795479)
              ·
                refine ⟨3542625205728923105693219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361750137152615403795479 3542625205728923105693219)
                ·
                  refine ⟨5313937808593384658539829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542625205728923105693219 5313937808593384658539829)
                  ·
                    refine ⟨498181669555629811738109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5313937808593384658539829 498181669555629811738109)
                    ·
                      rfl

theorem cell23_2910616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_2910616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910616 prefixEnd_2910616 := by exact prefixLift 2910616
  have htrace : WordTrace (prefixWord ++ tailWord_2910616) baseStart_2910616 baseEnd_2910616 := by
    simpa [prefixWord, tailWord_2910616, baseEnd_2910616] using wordTrace_append hprefix tailTrace_2910616
  have hstable : (prefixWord ++ tailWord_2910616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910616).length < 2 ^ (prefixWord ++ tailWord_2910616).sum := by decide
  have hdescent : baseEnd_2910616 < baseStart_2910616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910649 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2910649 : Nat := 118140960795 + 2910649 * 2 ^ 59
def prefixEnd_2910649 : Nat := 4983230072969 + 3 ^ 40 * 2910649 * 2
def baseEnd_2910649 : Nat := 1494561953528487806101675

theorem tailTrace_2910649 : CollatzResearch.WordTrace tailWord_2910649 prefixEnd_2910649 1494561953528487806101675 := by
  unfold tailWord_2910649
  simp only [CollatzResearch.WordTrace]
  refine ⟨106160090432223247118215001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70773393621482164745476667 106160090432223247118215001)
  ·
    refine ⟨79620067824167435338661251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106160090432223247118215001 79620067824167435338661251)
    ·
      refine ⟨119430101736251153007991877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79620067824167435338661251 119430101736251153007991877)
      ·
        refine ⟨22393144075547091188998477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119430101736251153007991877 22393144075547091188998477)
        ·
          refine ⟨8397429028330159195874429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22393144075547091188998477 8397429028330159195874429)
          ·
            refine ⟨3149035885623809698452911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8397429028330159195874429 3149035885623809698452911)
            ·
              refine ⟨4723553828435714547679367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149035885623809698452911 4723553828435714547679367)
              ·
                refine ⟨7085330742653571821519051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723553828435714547679367 7085330742653571821519051)
                ·
                  refine ⟨10627996113980357732278577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085330742653571821519051 10627996113980357732278577)
                  ·
                    refine ⟨7970997085485268299208933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10627996113980357732278577 7970997085485268299208933)
                    ·
                      refine ⟨1494561953528487806101675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7970997085485268299208933 1494561953528487806101675)
                      ·
                        rfl

theorem cell23_2910649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2910649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910649 prefixEnd_2910649 := by exact prefixLift 2910649
  have htrace : WordTrace (prefixWord ++ tailWord_2910649) baseStart_2910649 baseEnd_2910649 := by
    simpa [prefixWord, tailWord_2910649, baseEnd_2910649] using wordTrace_append hprefix tailTrace_2910649
  have hstable : (prefixWord ++ tailWord_2910649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910649).length < 2 ^ (prefixWord ++ tailWord_2910649).sum := by decide
  have hdescent : baseEnd_2910649 < baseStart_2910649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910665 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2910665 : Nat := 118140960795 + 2910665 * 2 ^ 59
def prefixEnd_2910665 : Nat := 4983230072969 + 3 ^ 40 * 2910665 * 2
def baseEnd_2910665 : Nat := 1494570169218959743501601

theorem tailTrace_2910665 : CollatzResearch.WordTrace tailWord_2910665 prefixEnd_2910665 1494570169218959743501601 := by
  unfold tailWord_2910665
  simp only [CollatzResearch.WordTrace]
  refine ⟨106160674000165281850797449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70773782666776854567198299 106160674000165281850797449)
  ·
    refine ⟨79620505500123961388098087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106160674000165281850797449 79620505500123961388098087)
    ·
      refine ⟨119430758250185942082147131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79620505500123961388098087 119430758250185942082147131)
      ·
        refine ⟨179146137375278913123220697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119430758250185942082147131 179146137375278913123220697)
        ·
          refine ⟨134359603031459184842415523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179146137375278913123220697 134359603031459184842415523)
          ·
            refine ⟨201539404547188777263623285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134359603031459184842415523 201539404547188777263623285)
            ·
              refine ⟨18894319176298947868464683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201539404547188777263623285 18894319176298947868464683)
              ·
                refine ⟨28341478764448421802697025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18894319176298947868464683 28341478764448421802697025)
                ·
                  refine ⟨21256109073336316352022769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28341478764448421802697025 21256109073336316352022769)
                  ·
                    refine ⟨15942081805002237264017077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21256109073336316352022769 15942081805002237264017077)
                    ·
                      refine ⟨1494570169218959743501601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15942081805002237264017077 1494570169218959743501601)
                      ·
                        rfl

theorem cell23_2910665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2910665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910665 prefixEnd_2910665 := by exact prefixLift 2910665
  have htrace : WordTrace (prefixWord ++ tailWord_2910665) baseStart_2910665 baseEnd_2910665 := by
    simpa [prefixWord, tailWord_2910665, baseEnd_2910665] using wordTrace_append hprefix tailTrace_2910665
  have hstable : (prefixWord ++ tailWord_2910665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910665).length < 2 ^ (prefixWord ++ tailWord_2910665).sum := by decide
  have hdescent : baseEnd_2910665 < baseStart_2910665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910756 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2910756 : Nat := 118140960795 + 2910756 * 2 ^ 59
def prefixEnd_2910756 : Nat := 4983230072969 + 3 ^ 40 * 2910756 * 2
def baseEnd_2910756 : Nat := 1494616895958518887463683

theorem tailTrace_2910756 : CollatzResearch.WordTrace tailWord_2910756 prefixEnd_2910756 1494616895958518887463683 := by
  unfold tailWord_2910756
  simp only [CollatzResearch.WordTrace]
  refine ⟨53081996521417802196180061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70775995361890402928240081 53081996521417802196180061)
  ·
    refine ⟨19905748695531675823567523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53081996521417802196180061 19905748695531675823567523)
    ·
      refine ⟨29858623043297513735351285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19905748695531675823567523 29858623043297513735351285)
      ·
        refine ⟨2799245910309141912689183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29858623043297513735351285 2799245910309141912689183)
        ·
          refine ⟨4198868865463712869033775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799245910309141912689183 4198868865463712869033775)
          ·
            refine ⟨6298303298195569303550663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198868865463712869033775 6298303298195569303550663)
            ·
              refine ⟨9447454947293353955325995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298303298195569303550663 9447454947293353955325995)
              ·
                refine ⟨14171182420940030932988993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9447454947293353955325995 14171182420940030932988993)
                ·
                  refine ⟨10628386815705023199741745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14171182420940030932988993 10628386815705023199741745)
                  ·
                    refine ⟨7971290111778767399806309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10628386815705023199741745 7971290111778767399806309)
                    ·
                      refine ⟨1494616895958518887463683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7971290111778767399806309 1494616895958518887463683)
                      ·
                        rfl

theorem cell23_2910756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2910756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910756 prefixEnd_2910756 := by exact prefixLift 2910756
  have htrace : WordTrace (prefixWord ++ tailWord_2910756) baseStart_2910756 baseEnd_2910756 := by
    simpa [prefixWord, tailWord_2910756, baseEnd_2910756] using wordTrace_append hprefix tailTrace_2910756
  have hstable : (prefixWord ++ tailWord_2910756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910756).length < 2 ^ (prefixWord ++ tailWord_2910756).sum := by decide
  have hdescent : baseEnd_2910756 < baseStart_2910756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910799 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 4, 2]
def baseStart_2910799 : Nat := 118140960795 + 2910799 * 2 ^ 59
def prefixEnd_2910799 : Nat := 4983230072969 + 3 ^ 40 * 2910799 * 2
def baseEnd_2910799 : Nat := 1494638975626662219225985

theorem tailTrace_2910799 : CollatzResearch.WordTrace tailWord_2910799 prefixEnd_2910799 1494638975626662219225985 := by
  unfold tailWord_2910799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106165561381679822736175451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70777040921119881824116967 106165561381679822736175451)
  ·
    refine ⟨159248342072519734104263177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106165561381679822736175451 159248342072519734104263177)
    ·
      refine ⟨119436256554389800578197383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159248342072519734104263177 119436256554389800578197383)
      ·
        refine ⟨179154384831584700867296075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119436256554389800578197383 179154384831584700867296075)
        ·
          refine ⟨268731577247377051300944113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179154384831584700867296075 268731577247377051300944113)
          ·
            refine ⟨201548682935532788475708085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268731577247377051300944113 201548682935532788475708085)
            ·
              refine ⟨18895189025206198919597633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201548682935532788475708085 18895189025206198919597633)
              ·
                refine ⟨14171391768904649189698225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18895189025206198919597633 14171391768904649189698225)
                ·
                  refine ⟨10628543826678486892273669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14171391768904649189698225 10628543826678486892273669)
                  ·
                    refine ⟨1992851967502216292301313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10628543826678486892273669 1992851967502216292301313)
                    ·
                      refine ⟨1494638975626662219225985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992851967502216292301313 1494638975626662219225985)
                      ·
                        rfl

theorem cell23_2910799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4, 2].length) (baseStart_2910799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910799 prefixEnd_2910799 := by exact prefixLift 2910799
  have htrace : WordTrace (prefixWord ++ tailWord_2910799) baseStart_2910799 baseEnd_2910799 := by
    simpa [prefixWord, tailWord_2910799, baseEnd_2910799] using wordTrace_append hprefix tailTrace_2910799
  have hstable : (prefixWord ++ tailWord_2910799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910799).length < 2 ^ (prefixWord ++ tailWord_2910799).sum := by decide
  have hdescent : baseEnd_2910799 < baseStart_2910799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910859 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 5, 2]
def baseStart_2910859 : Nat := 118140960795 + 2910859 * 2 ^ 59
def prefixEnd_2910859 : Nat := 4983230072969 + 3 ^ 40 * 2910859 * 2
def baseEnd_2910859 : Nat := 1494669784465931984475709

theorem tailTrace_2910859 : CollatzResearch.WordTrace tailWord_2910859 prefixEnd_2910859 1494669784465931984475709 := by
  unfold tailWord_2910859
  simp only [CollatzResearch.WordTrace]
  refine ⟨106167749761462452983359631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70778499840974968655573087 106167749761462452983359631)
  ·
    refine ⟨159251624642193679475039447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106167749761462452983359631 159251624642193679475039447)
    ·
      refine ⟨238877436963290519212559171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159251624642193679475039447 238877436963290519212559171)
      ·
        refine ⟨358316155444935778818838757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238877436963290519212559171 358316155444935778818838757)
        ·
          refine ⟨67184279145925458528532267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358316155444935778818838757 67184279145925458528532267)
          ·
            refine ⟨100776418718888187792798401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67184279145925458528532267 100776418718888187792798401)
            ·
              refine ⟨75582314039166140844598801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100776418718888187792798401 75582314039166140844598801)
              ·
                refine ⟨56686735529374605633449101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75582314039166140844598801 56686735529374605633449101)
                ·
                  refine ⟨21257525823515477112543413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56686735529374605633449101 21257525823515477112543413)
                  ·
                    refine ⟨1992893045954575979300945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21257525823515477112543413 1992893045954575979300945)
                    ·
                      refine ⟨1494669784465931984475709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992893045954575979300945 1494669784465931984475709)
                      ·
                        rfl

theorem cell23_2910859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5, 2].length) (baseStart_2910859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910859 prefixEnd_2910859 := by exact prefixLift 2910859
  have htrace : WordTrace (prefixWord ++ tailWord_2910859) baseStart_2910859 baseEnd_2910859 := by
    simpa [prefixWord, tailWord_2910859, baseEnd_2910859] using wordTrace_append hprefix tailTrace_2910859
  have hstable : (prefixWord ++ tailWord_2910859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910859).length < 2 ^ (prefixWord ++ tailWord_2910859).sum := by decide
  have hdescent : baseEnd_2910859 < baseStart_2910859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910889 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 8, 2]
def baseStart_2910889 : Nat := 118140960795 + 2910889 * 2 ^ 59
def prefixEnd_2910889 : Nat := 4983230072969 + 3 ^ 40 * 2910889 * 2
def baseEnd_2910889 : Nat := 1494685188885566867100571

theorem tailTrace_2910889 : CollatzResearch.WordTrace tailWord_2910889 prefixEnd_2910889 1494685188885566867100571 := by
  unfold tailWord_2910889
  simp only [CollatzResearch.WordTrace]
  refine ⟨106168843951353768106951721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70779229300902512071301147 106168843951353768106951721)
  ·
    refine ⟨79626632963515326080213791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106168843951353768106951721 79626632963515326080213791)
    ·
      refine ⟨119439949445272989120320687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79626632963515326080213791 119439949445272989120320687)
      ·
        refine ⟨179159924167909483680481031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119439949445272989120320687 179159924167909483680481031)
        ·
          refine ⟨268739886251864225520721547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179159924167909483680481031 268739886251864225520721547)
          ·
            refine ⟨403109829377796338281082321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268739886251864225520721547 403109829377796338281082321)
            ·
              refine ⟨302332372033347253710811741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403109829377796338281082321 302332372033347253710811741)
              ·
                refine ⟨113374639512505220141554403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302332372033347253710811741 113374639512505220141554403)
                ·
                  refine ⟨170061959268757830212331605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113374639512505220141554403 170061959268757830212331605)
                  ·
                    refine ⟨1992913585180755822800761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 170061959268757830212331605 1992913585180755822800761)
                    ·
                      refine ⟨1494685188885566867100571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992913585180755822800761 1494685188885566867100571)
                      ·
                        rfl

theorem cell23_2910889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8, 2].length) (baseStart_2910889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910889 prefixEnd_2910889 := by exact prefixLift 2910889
  have htrace : WordTrace (prefixWord ++ tailWord_2910889) baseStart_2910889 baseEnd_2910889 := by
    simpa [prefixWord, tailWord_2910889, baseEnd_2910889] using wordTrace_append hprefix tailTrace_2910889
  have hstable : (prefixWord ++ tailWord_2910889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910889).length < 2 ^ (prefixWord ++ tailWord_2910889).sum := by decide
  have hdescent : baseEnd_2910889 < baseStart_2910889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910892 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2910892 : Nat := 118140960795 + 2910892 * 2 ^ 59
def prefixEnd_2910892 : Nat := 4983230072969 + 3 ^ 40 * 2910892 * 2
def baseEnd_2910892 : Nat := 1494686729327530355363057

theorem tailTrace_2910892 : CollatzResearch.WordTrace tailWord_2910892 prefixEnd_2910892 1494686729327530355363057 := by
  unfold tailWord_2910892
  simp only [CollatzResearch.WordTrace]
  refine ⟨53084476685171449809655465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70779302246895266412873953 53084476685171449809655465)
  ·
    refine ⟨39813357513878587357241599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53084476685171449809655465 39813357513878587357241599)
    ·
      refine ⟨59720036270817881035862399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39813357513878587357241599 59720036270817881035862399)
      ·
        refine ⟨89580054406226821553793599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59720036270817881035862399 89580054406226821553793599)
        ·
          refine ⟨134370081609340232330690399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89580054406226821553793599 134370081609340232330690399)
          ·
            refine ⟨201555122414010348496035599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134370081609340232330690399 201555122414010348496035599)
            ·
              refine ⟨302332683621015522744053399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201555122414010348496035599 302332683621015522744053399)
              ·
                refine ⟨453499025431523284116080099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302332683621015522744053399 453499025431523284116080099)
                ·
                  refine ⟨680248538147284926174120149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453499025431523284116080099 680248538147284926174120149)
                  ·
                    refine ⟨15943325112826990457205941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 680248538147284926174120149 15943325112826990457205941)
                    ·
                      refine ⟨1494686729327530355363057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15943325112826990457205941 1494686729327530355363057)
                      ·
                        rfl

theorem cell23_2910892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2910892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910892 prefixEnd_2910892 := by exact prefixLift 2910892
  have htrace : WordTrace (prefixWord ++ tailWord_2910892) baseStart_2910892 baseEnd_2910892 := by
    simpa [prefixWord, tailWord_2910892, baseEnd_2910892] using wordTrace_append hprefix tailTrace_2910892
  have hstable : (prefixWord ++ tailWord_2910892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910892).length < 2 ^ (prefixWord ++ tailWord_2910892).sum := by decide
  have hdescent : baseEnd_2910892 < baseStart_2910892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910893 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_2910893 : Nat := 118140960795 + 2910893 * 2 ^ 59
def prefixEnd_2910893 : Nat := 4983230072969 + 3 ^ 40 * 2910893 * 2
def baseEnd_2910893 : Nat := 1494687242808184851450553

theorem tailTrace_2910893 : CollatzResearch.WordTrace tailWord_2910893 prefixEnd_2910893 1494687242808184851450553 := by
  unfold tailWord_2910893
  simp only [CollatzResearch.WordTrace]
  refine ⟨106168989843339276790097333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70779326562226184526731555 106168989843339276790097333)
  ·
    refine ⟨9953342797813057199071625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106168989843339276790097333 9953342797813057199071625)
    ·
      refine ⟨7465007098359792899303719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9953342797813057199071625 7465007098359792899303719)
      ·
        refine ⟨11197510647539689348955579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465007098359792899303719 11197510647539689348955579)
        ·
          refine ⟨16796265971309534023433369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197510647539689348955579 16796265971309534023433369)
          ·
            refine ⟨12597199478482150517575027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16796265971309534023433369 12597199478482150517575027)
            ·
              refine ⟨18895799217723225776362541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597199478482150517575027 18895799217723225776362541)
              ·
                refine ⟨7085924706646209666135953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18895799217723225776362541 7085924706646209666135953)
                ·
                  refine ⟨5314443529984657249601965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085924706646209666135953 5314443529984657249601965)
                  ·
                    refine ⟨1992916323744246468600737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5314443529984657249601965 1992916323744246468600737)
                    ·
                      refine ⟨1494687242808184851450553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1992916323744246468600737 1494687242808184851450553)
                      ·
                        rfl

theorem cell23_2910893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_2910893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910893 prefixEnd_2910893 := by exact prefixLift 2910893
  have htrace : WordTrace (prefixWord ++ tailWord_2910893) baseStart_2910893 baseEnd_2910893 := by
    simpa [prefixWord, tailWord_2910893, baseEnd_2910893] using wordTrace_append hprefix tailTrace_2910893
  have hstable : (prefixWord ++ tailWord_2910893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910893).length < 2 ^ (prefixWord ++ tailWord_2910893).sum := by decide
  have hdescent : baseEnd_2910893 < baseStart_2910893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910899 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 6]
def baseStart_2910899 : Nat := 118140960795 + 2910899 * 2 ^ 59
def prefixEnd_2910899 : Nat := 4983230072969 + 3 ^ 40 * 2910899 * 2
def baseEnd_2910899 : Nat := 498230107897370609325175

theorem tailTrace_2910899 : CollatzResearch.WordTrace tailWord_2910899 prefixEnd_2910899 498230107897370609325175 := by
  unfold tailWord_2910899
  simp only [CollatzResearch.WordTrace]
  refine ⟨106169208681317539814815751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70779472454211693209877167 106169208681317539814815751)
  ·
    refine ⟨159253813021976309722223627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106169208681317539814815751 159253813021976309722223627)
    ·
      refine ⟨238880719532964464583335441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159253813021976309722223627 238880719532964464583335441)
      ·
        refine ⟨179160539649723348437501581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238880719532964464583335441 179160539649723348437501581)
        ·
          refine ⟨67185202368646255664063093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179160539649723348437501581 67185202368646255664063093)
          ·
            refine ⟨6298612722060586468505915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67185202368646255664063093 6298612722060586468505915)
            ·
              refine ⟨9447919083090879702758873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298612722060586468505915 9447919083090879702758873)
              ·
                refine ⟨7085939312318159777069155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9447919083090879702758873 7085939312318159777069155)
                ·
                  refine ⟨10628908968477239665603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085939312318159777069155 10628908968477239665603733)
                  ·
                    refine ⟨498230107897370609325175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10628908968477239665603733 498230107897370609325175)
                    ·
                      rfl

theorem cell23_2910899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_2910899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910899 prefixEnd_2910899 := by exact prefixLift 2910899
  have htrace : WordTrace (prefixWord ++ tailWord_2910899) baseStart_2910899 baseEnd_2910899 := by
    simpa [prefixWord, tailWord_2910899, baseEnd_2910899] using wordTrace_append hprefix tailTrace_2910899
  have hstable : (prefixWord ++ tailWord_2910899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910899).length < 2 ^ (prefixWord ++ tailWord_2910899).sum := by decide
  have hdescent : baseEnd_2910899 < baseStart_2910899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910903 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 1, 5]
def baseStart_2910903 : Nat := 118140960795 + 2910903 * 2 ^ 59
def prefixEnd_2910903 : Nat := 4983230072969 + 3 ^ 40 * 2910903 * 2
def baseEnd_2910903 : Nat := 498230792538243270775169

theorem tailTrace_2910903 : CollatzResearch.WordTrace tailWord_2910903 prefixEnd_2910903 498230792538243270775169 := by
  unfold tailWord_2910903
  simp only [CollatzResearch.WordTrace]
  refine ⟨106169354573303048497961363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70779569715535365665307575 106169354573303048497961363)
  ·
    refine ⟨159254031859954572746942045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106169354573303048497961363 159254031859954572746942045)
    ·
      refine ⟨59720261947482964780103267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159254031859954572746942045 59720261947482964780103267)
      ·
        refine ⟨89580392921224447170154901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59720261947482964780103267 89580392921224447170154901)
        ·
          refine ⟨4199080918182395961101011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89580392921224447170154901 4199080918182395961101011)
          ·
            refine ⟨6298621377273593941651517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199080918182395961101011 6298621377273593941651517)
            ·
              refine ⟨2361983016477597728119319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6298621377273593941651517 2361983016477597728119319)
              ·
                refine ⟨3542974524716396592178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361983016477597728119319 3542974524716396592178979)
                ·
                  refine ⟨5314461787074594888268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542974524716396592178979 5314461787074594888268469)
                  ·
                    refine ⟨498230792538243270775169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5314461787074594888268469 498230792538243270775169)
                    ·
                      rfl

theorem cell23_2910903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_2910903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910903 prefixEnd_2910903 := by exact prefixLift 2910903
  have htrace : WordTrace (prefixWord ++ tailWord_2910903) baseStart_2910903 baseEnd_2910903 := by
    simpa [prefixWord, tailWord_2910903, baseEnd_2910903] using wordTrace_append hprefix tailTrace_2910903
  have hstable : (prefixWord ++ tailWord_2910903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910903).length < 2 ^ (prefixWord ++ tailWord_2910903).sum := by decide
  have hdescent : baseEnd_2910903 < baseStart_2910903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910912 : List Nat := [2, 1, 1, 2, 4, 13]
def baseStart_2910912 : Nat := 118140960795 + 2910912 * 2 ^ 59
def prefixEnd_2910912 : Nat := 4983230072969 + 3 ^ 40 * 2910912 * 2
def baseEnd_2910912 : Nat := 6151016456545762457255

theorem tailTrace_2910912 : CollatzResearch.WordTrace tailWord_2910912 prefixEnd_2910912 6151016456545762457255 := by
  unfold tailWord_2910912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53084841415135221517519495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70779788553513628690025993 53084841415135221517519495)
  ·
    refine ⟨79627262122702832276279243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53084841415135221517519495 79627262122702832276279243)
    ·
      refine ⟨119440893184054248414418865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79627262122702832276279243 119440893184054248414418865)
      ·
        refine ⟨89580669888040686310814149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119440893184054248414418865 89580669888040686310814149)
        ·
          refine ⟨16796375604007628683277653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89580669888040686310814149 16796375604007628683277653)
          ·
            refine ⟨6151016456545762457255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16796375604007628683277653 6151016456545762457255)
            ·
              rfl

theorem cell23_2910912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 13].length) (baseStart_2910912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2910912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2910912 prefixEnd_2910912 := by exact prefixLift 2910912
  have htrace : WordTrace (prefixWord ++ tailWord_2910912) baseStart_2910912 baseEnd_2910912 := by
    simpa [prefixWord, tailWord_2910912, baseEnd_2910912] using wordTrace_append hprefix tailTrace_2910912
  have hstable : (prefixWord ++ tailWord_2910912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910912).length < 2 ^ (prefixWord ++ tailWord_2910912).sum := by decide
  have hdescent : baseEnd_2910912 < baseStart_2910912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
