import V185TrunkScan23Chunk1053

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6240156 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6240156 : Nat := 118140960795 + 6240156 * 2 ^ 59
def prefixEnd_6240156 : Nat := 4983230072969 + 3 ^ 40 * 6240156 * 2
def baseEnd_6240156 : Nat := 1068066462345930864884017

theorem tailTrace_6240156 : CollatzResearch.WordTrace tailWord_6240156 prefixEnd_6240156 1068066462345930864884017 := by
  unfold tailWord_6240156
  simp only [CollatzResearch.WordTrace]
  refine ⟨113798593590494010321254161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151731458120658680428338881 113798593590494010321254161)
  ·
    refine ⟨85348945192870507740940621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113798593590494010321254161 85348945192870507740940621)
    ·
      refine ⟨32005854447326440402852733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85348945192870507740940621 32005854447326440402852733)
      ·
        refine ⟨12002195417747415151069775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32005854447326440402852733 12002195417747415151069775)
        ·
          refine ⟨18003293126621122726604663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002195417747415151069775 18003293126621122726604663)
          ·
            refine ⟨27004939689931684089906995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18003293126621122726604663 27004939689931684089906995)
            ·
              refine ⟨40507409534897526134860493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27004939689931684089906995 40507409534897526134860493)
              ·
                refine ⟨15190278575586572300572685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40507409534897526134860493 15190278575586572300572685)
                ·
                  refine ⟨5696354465844964612714757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15190278575586572300572685 5696354465844964612714757)
                  ·
                    refine ⟨1068066462345930864884017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696354465844964612714757 1068066462345930864884017)
                    ·
                      rfl

theorem cell23_6240156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6240156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240156 prefixEnd_6240156 := by exact prefixLift 6240156
  have htrace : WordTrace (prefixWord ++ tailWord_6240156) baseStart_6240156 baseEnd_6240156 := by
    simpa [prefixWord, tailWord_6240156, baseEnd_6240156] using wordTrace_append hprefix tailTrace_6240156
  have hstable : (prefixWord ++ tailWord_6240156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240156).length < 2 ^ (prefixWord ++ tailWord_6240156).sum := by decide
  have hdescent : baseEnd_6240156 < baseStart_6240156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240190 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_6240190 : Nat := 118140960795 + 6240190 * 2 ^ 59
def prefixEnd_6240190 : Nat := 4983230072969 + 3 ^ 40 * 6240190 * 2
def baseEnd_6240190 : Nat := 1068072281793348487208965

theorem tailTrace_6240190 : CollatzResearch.WordTrace tailWord_6240190 prefixEnd_6240190 1068072281793348487208965 := by
  unfold tailWord_6240190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449803407858105556155753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151732284841909896299497349 28449803407858105556155753)
  ·
    refine ⟨21337352555893579167116815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28449803407858105556155753 21337352555893579167116815)
    ·
      refine ⟨32006028833840368750675223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21337352555893579167116815 32006028833840368750675223)
      ·
        refine ⟨48009043250760553126012835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32006028833840368750675223 48009043250760553126012835)
        ·
          refine ⟨72013564876140829689019253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48009043250760553126012835 72013564876140829689019253)
          ·
            refine ⟨6751271707138202783345555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72013564876140829689019253 6751271707138202783345555)
            ·
              refine ⟨10126907560707304175018333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751271707138202783345555 10126907560707304175018333)
              ·
                refine ⟨3797590335265239065631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10126907560707304175018333 3797590335265239065631875)
                ·
                  refine ⟨5696385502897858598447813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797590335265239065631875 5696385502897858598447813)
                  ·
                    refine ⟨1068072281793348487208965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696385502897858598447813 1068072281793348487208965)
                    ·
                      rfl

theorem cell23_6240190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_6240190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240190 prefixEnd_6240190 := by exact prefixLift 6240190
  have htrace : WordTrace (prefixWord ++ tailWord_6240190) baseStart_6240190 baseEnd_6240190 := by
    simpa [prefixWord, tailWord_6240190, baseEnd_6240190] using wordTrace_append hprefix tailTrace_6240190
  have hstable : (prefixWord ++ tailWord_6240190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240190).length < 2 ^ (prefixWord ++ tailWord_6240190).sum := by decide
  have hdescent : baseEnd_6240190 < baseStart_6240190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240213 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6240213 : Nat := 118140960795 + 6240213 * 2 ^ 59
def prefixEnd_6240213 : Nat := 4983230072969 + 3 ^ 40 * 6240213 * 2
def baseEnd_6240213 : Nat := 3204228655435098871639289

theorem tailTrace_6240213 : CollatzResearch.WordTrace tailWord_6240213 prefixEnd_6240213 3204228655435098871639289 := by
  unfold tailWord_6240213
  simp only [CollatzResearch.WordTrace]
  refine ⟨227599266141781519377333293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151732844094521012918222195 227599266141781519377333293)
  ·
    refine ⟨85349724803168069766499985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227599266141781519377333293 85349724803168069766499985)
    ·
      refine ⟨64012293602376052324874989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85349724803168069766499985 64012293602376052324874989)
      ·
        refine ⟨24004610100891019621828121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64012293602376052324874989 24004610100891019621828121)
        ·
          refine ⟨18003457575668264716371091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24004610100891019621828121 18003457575668264716371091)
          ·
            refine ⟨27005186363502397074556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18003457575668264716371091 27005186363502397074556637)
            ·
              refine ⟨10126944886313398902958739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27005186363502397074556637 10126944886313398902958739)
              ·
                refine ⟨15190417329470098354438109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10126944886313398902958739 15190417329470098354438109)
                ·
                  refine ⟨5696406498551286882914291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15190417329470098354438109 5696406498551286882914291)
                  ·
                    refine ⟨8544609747826930324371437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696406498551286882914291 8544609747826930324371437)
                    ·
                      refine ⟨3204228655435098871639289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8544609747826930324371437 3204228655435098871639289)
                      ·
                        rfl

theorem cell23_6240213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6240213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240213 prefixEnd_6240213 := by exact prefixLift 6240213
  have htrace : WordTrace (prefixWord ++ tailWord_6240213) baseStart_6240213 baseEnd_6240213 := by
    simpa [prefixWord, tailWord_6240213, baseEnd_6240213] using wordTrace_append hprefix tailTrace_6240213
  have hstable : (prefixWord ++ tailWord_6240213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240213).length < 2 ^ (prefixWord ++ tailWord_6240213).sum := by decide
  have hdescent : baseEnd_6240213 < baseStart_6240213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240220 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 6]
def baseStart_6240220 : Nat := 118140960795 + 6240220 * 2 ^ 59
def prefixEnd_6240220 : Nat := 4983230072969 + 3 ^ 40 * 6240220 * 2
def baseEnd_6240220 : Nat := 356025805533297816027973

theorem tailTrace_6240220 : CollatzResearch.WordTrace tailWord_6240220 prefixEnd_6240220 356025805533297816027973 := by
  unfold tailWord_6240220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113799760726378079786419057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151733014301837439715225409 113799760726378079786419057)
  ·
    refine ⟨85349820544783559839814293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113799760726378079786419057 85349820544783559839814293)
    ·
      refine ⟨4000772838036729367491295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85349820544783559839814293 4000772838036729367491295)
      ·
        refine ⟨6001159257055094051236943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000772838036729367491295 6001159257055094051236943)
        ·
          refine ⟨9001738885582641076855415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001159257055094051236943 9001738885582641076855415)
          ·
            refine ⟨13502608328373961615283123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001738885582641076855415 13502608328373961615283123)
            ·
              refine ⟨20253912492560942422924685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13502608328373961615283123 20253912492560942422924685)
              ·
                refine ⟨7595217184710353408596757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20253912492560942422924685 7595217184710353408596757)
                ·
                  refine ⟨356025805533297816027973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7595217184710353408596757 356025805533297816027973)
                  ·
                    rfl

theorem cell23_6240220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_6240220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240220 prefixEnd_6240220 := by exact prefixLift 6240220
  have htrace : WordTrace (prefixWord ++ tailWord_6240220) baseStart_6240220 baseEnd_6240220 := by
    simpa [prefixWord, tailWord_6240220, baseEnd_6240220] using wordTrace_append hprefix tailTrace_6240220
  have hstable : (prefixWord ++ tailWord_6240220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240220).length < 2 ^ (prefixWord ++ tailWord_6240220).sum := by decide
  have hdescent : baseEnd_6240220 < baseStart_6240220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240249 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6240249 : Nat := 118140960795 + 6240249 * 2 ^ 59
def prefixEnd_6240249 : Nat := 4983230072969 + 3 ^ 40 * 6240249 * 2
def baseEnd_6240249 : Nat := 3204247140738660730789123

theorem tailTrace_6240249 : CollatzResearch.WordTrace tailWord_6240249 prefixEnd_6240249 3204247140738660730789123 := by
  unfold tailWord_6240249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227600579169651097525643801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151733719446434065017095867 227600579169651097525643801)
  ·
    refine ⟨170700434377238323144232851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227600579169651097525643801 170700434377238323144232851)
    ·
      refine ⟨256050651565857484716349277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170700434377238323144232851 256050651565857484716349277)
      ·
        refine ⟨96018994337196556768630979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256050651565857484716349277 96018994337196556768630979)
        ·
          refine ⟨144028491505794835152946469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96018994337196556768630979 144028491505794835152946469)
          ·
            refine ⟨27005342157336531591177463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144028491505794835152946469 27005342157336531591177463)
            ·
              refine ⟨40508013236004797386766195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27005342157336531591177463 40508013236004797386766195)
              ·
                refine ⟨60762019854007196080149293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40508013236004797386766195 60762019854007196080149293)
                ·
                  refine ⟨22785757445252698530055985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60762019854007196080149293 22785757445252698530055985)
                  ·
                    refine ⟨17089318083939523897541989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22785757445252698530055985 17089318083939523897541989)
                    ·
                      refine ⟨3204247140738660730789123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17089318083939523897541989 3204247140738660730789123)
                      ·
                        rfl

theorem cell23_6240249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6240249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240249 prefixEnd_6240249 := by exact prefixLift 6240249
  have htrace : WordTrace (prefixWord ++ tailWord_6240249) baseStart_6240249 baseEnd_6240249 := by
    simpa [prefixWord, tailWord_6240249, baseEnd_6240249] using wordTrace_append hprefix tailTrace_6240249
  have hstable : (prefixWord ++ tailWord_6240249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240249).length < 2 ^ (prefixWord ++ tailWord_6240249).sum := by decide
  have hdescent : baseEnd_6240249 < baseStart_6240249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240263 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 2, 4]
def baseStart_6240263 : Nat := 118140960795 + 6240263 * 2 ^ 59
def prefixEnd_6240263 : Nat := 4983230072969 + 3 ^ 40 * 6240263 * 2
def baseEnd_6240263 : Nat := 1068084776489274558671353

theorem tailTrace_6240263 : CollatzResearch.WordTrace tailWord_6240263 prefixEnd_6240263 1068084776489274558671353 := by
  unfold tailWord_6240263
  simp only [CollatzResearch.WordTrace]
  refine ⟨227601089791600377916653443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151734059861066918611102295 227601089791600377916653443)
  ·
    refine ⟨341401634687400566874980165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227601089791600377916653443 341401634687400566874980165)
    ·
      refine ⟨64012806503887606289058781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341401634687400566874980165 64012806503887606289058781)
      ·
        refine ⟨24004802438957852358397043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64012806503887606289058781 24004802438957852358397043)
        ·
          refine ⟨36007203658436778537595565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24004802438957852358397043 36007203658436778537595565)
          ·
            refine ⟨13502701371913791951598337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36007203658436778537595565 13502701371913791951598337)
            ·
              refine ⟨10127026028935343963698753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13502701371913791951598337 10127026028935343963698753)
              ·
                refine ⟨7595269521701507972774065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10127026028935343963698753 7595269521701507972774065)
                ·
                  refine ⟨5696452141276130979580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7595269521701507972774065 5696452141276130979580549)
                  ·
                    refine ⟨1068084776489274558671353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696452141276130979580549 1068084776489274558671353)
                    ·
                      rfl

theorem cell23_6240263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_6240263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240263 prefixEnd_6240263 := by exact prefixLift 6240263
  have htrace : WordTrace (prefixWord ++ tailWord_6240263) baseStart_6240263 baseEnd_6240263 := by
    simpa [prefixWord, tailWord_6240263, baseEnd_6240263] using wordTrace_append hprefix tailTrace_6240263
  have hstable : (prefixWord ++ tailWord_6240263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240263).length < 2 ^ (prefixWord ++ tailWord_6240263).sum := by decide
  have hdescent : baseEnd_6240263 < baseStart_6240263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240319 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 6]
def baseStart_6240319 : Nat := 118140960795 + 6240319 * 2 ^ 59
def prefixEnd_6240319 : Nat := 4983230072969 + 3 ^ 40 * 6240319 * 2
def baseEnd_6240319 : Nat := 1068094361461491818971267

theorem tailTrace_6240319 : CollatzResearch.WordTrace tailWord_6240319 prefixEnd_6240319 1068094361461491818971267 := by
  unfold tailWord_6240319
  simp only [CollatzResearch.WordTrace]
  refine ⟨227603132279397499480692011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151735421519598332987128007 227603132279397499480692011)
  ·
    refine ⟨341404698419096249221038017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227603132279397499480692011 341404698419096249221038017)
    ·
      refine ⟨256053523814322186915778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341404698419096249221038017 256053523814322186915778513)
      ·
        refine ⟨192040142860741640186833885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256053523814322186915778513 192040142860741640186833885)
        ·
          refine ⟨72015053572778115070062707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192040142860741640186833885 72015053572778115070062707)
          ·
            refine ⟨108022580359167172605094061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72015053572778115070062707 108022580359167172605094061)
            ·
              refine ⟨40508467634687689726910273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108022580359167172605094061 40508467634687689726910273)
              ·
                refine ⟨30381350726015767295182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40508467634687689726910273 30381350726015767295182705)
                ·
                  refine ⟨22786013044511825471387029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30381350726015767295182705 22786013044511825471387029)
                  ·
                    refine ⟨1068094361461491818971267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22786013044511825471387029 1068094361461491818971267)
                    ·
                      rfl

theorem cell23_6240319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_6240319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240319 prefixEnd_6240319 := by exact prefixLift 6240319
  have htrace : WordTrace (prefixWord ++ tailWord_6240319) baseStart_6240319 baseEnd_6240319 := by
    simpa [prefixWord, tailWord_6240319, baseEnd_6240319] using wordTrace_append hprefix tailTrace_6240319
  have hstable : (prefixWord ++ tailWord_6240319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240319).length < 2 ^ (prefixWord ++ tailWord_6240319).sum := by decide
  have hdescent : baseEnd_6240319 < baseStart_6240319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240320 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_6240320 : Nat := 118140960795 + 6240320 * 2 ^ 59
def prefixEnd_6240320 : Nat := 4983230072969 + 3 ^ 40 * 6240320 * 2
def baseEnd_6240320 : Nat := 3204283597865129953001297

theorem tailTrace_6240320 : CollatzResearch.WordTrace tailWord_6240320 prefixEnd_6240320 3204283597865129953001297 := by
  unfold tailWord_6240320
  simp only [CollatzResearch.WordTrace]
  refine ⟨113801584376196938325739207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151735445834929251100985609 113801584376196938325739207)
  ·
    refine ⟨170702376564295407488608811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113801584376196938325739207 170702376564295407488608811)
    ·
      refine ⟨256053564846443111232913217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170702376564295407488608811 256053564846443111232913217)
      ·
        refine ⟨192040173634832333424684913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256053564846443111232913217 192040173634832333424684913)
        ·
          refine ⟨144030130226124250068513685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192040173634832333424684913 144030130226124250068513685)
          ·
            refine ⟨6751412354349574221961579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144030130226124250068513685 6751412354349574221961579)
            ·
              refine ⟨10127118531524361332942369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751412354349574221961579 10127118531524361332942369)
              ·
                refine ⟨7595338898643270999706777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10127118531524361332942369 7595338898643270999706777)
                ·
                  refine ⟨5696504173982453249780083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7595338898643270999706777 5696504173982453249780083)
                  ·
                    refine ⟨8544756260973679874670125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696504173982453249780083 8544756260973679874670125)
                    ·
                      refine ⟨3204283597865129953001297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8544756260973679874670125 3204283597865129953001297)
                      ·
                        rfl

theorem cell23_6240320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_6240320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240320 prefixEnd_6240320 := by exact prefixLift 6240320
  have htrace : WordTrace (prefixWord ++ tailWord_6240320) baseStart_6240320 baseEnd_6240320 := by
    simpa [prefixWord, tailWord_6240320, baseEnd_6240320] using wordTrace_append hprefix tailTrace_6240320
  have hstable : (prefixWord ++ tailWord_6240320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240320).length < 2 ^ (prefixWord ++ tailWord_6240320).sum := by decide
  have hdescent : baseEnd_6240320 < baseStart_6240320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240339 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_6240339 : Nat := 118140960795 + 6240339 * 2 ^ 59
def prefixEnd_6240339 : Nat := 4983230072969 + 3 ^ 40 * 6240339 * 2
def baseEnd_6240339 : Nat := 3204293353997565378663709

theorem tailTrace_6240339 : CollatzResearch.WordTrace tailWord_6240339 prefixEnd_6240339 3204293353997565378663709 := by
  unfold tailWord_6240339
  simp only [CollatzResearch.WordTrace]
  refine ⟨227603861739325042896420071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151735907826216695264280047 227603861739325042896420071)
  ·
    refine ⟨341405792608987564344630107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227603861739325042896420071 341405792608987564344630107)
    ·
      refine ⟨512108688913481346516945161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341405792608987564344630107 512108688913481346516945161)
      ·
        refine ⟨384081516685111009887708871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512108688913481346516945161 384081516685111009887708871)
        ·
          refine ⟨576122275027666514831563307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384081516685111009887708871 576122275027666514831563307)
          ·
            refine ⟨864183412541499772247344961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576122275027666514831563307 864183412541499772247344961)
            ·
              refine ⟨648137559406124829185508721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864183412541499772247344961 648137559406124829185508721)
              ·
                refine ⟨486103169554593621889131541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648137559406124829185508721 486103169554593621889131541)
                ·
                  refine ⟨22786086072871576026053041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 486103169554593621889131541 22786086072871576026053041)
                  ·
                    refine ⟨17089564554653682019539781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22786086072871576026053041 17089564554653682019539781)
                    ·
                      refine ⟨3204293353997565378663709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17089564554653682019539781 3204293353997565378663709)
                      ·
                        rfl

theorem cell23_6240339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_6240339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240339 prefixEnd_6240339 := by exact prefixLift 6240339
  have htrace : WordTrace (prefixWord ++ tailWord_6240339) baseStart_6240339 baseEnd_6240339 := by
    simpa [prefixWord, tailWord_6240339, baseEnd_6240339] using wordTrace_append hprefix tailTrace_6240339
  have hstable : (prefixWord ++ tailWord_6240339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240339).length < 2 ^ (prefixWord ++ tailWord_6240339).sum := by decide
  have hdescent : baseEnd_6240339 < baseStart_6240339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240343 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_6240343 : Nat := 118140960795 + 6240343 * 2 ^ 59
def prefixEnd_6240343 : Nat := 4983230072969 + 3 ^ 40 * 6240343 * 2
def baseEnd_6240343 : Nat := 3204295407920183363013691

theorem tailTrace_6240343 : CollatzResearch.WordTrace tailWord_6240343 prefixEnd_6240343 3204295407920183363013691 := by
  unfold tailWord_6240343
  simp only [CollatzResearch.WordTrace]
  refine ⟨227604007631310551579565683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151736005087540367719710455 227604007631310551579565683)
  ·
    refine ⟨341406011446965827369348525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227604007631310551579565683 341406011446965827369348525)
    ·
      refine ⟨128027254292612185263505697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341406011446965827369348525 128027254292612185263505697)
      ·
        refine ⟨96020440719459138947629273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128027254292612185263505697 96020440719459138947629273)
        ·
          refine ⟨72015330539594354210721955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96020440719459138947629273 72015330539594354210721955)
          ·
            refine ⟨108022995809391531316082933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72015330539594354210721955 108022995809391531316082933)
            ·
              refine ⟨10127155857130456060882775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108022995809391531316082933 10127155857130456060882775)
              ·
                refine ⟨15190733785695684091324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10127155857130456060882775 15190733785695684091324163)
                ·
                  refine ⟨22786100678543526136986245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15190733785695684091324163 22786100678543526136986245)
                  ·
                    refine ⟨4272393877226911150684921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22786100678543526136986245 4272393877226911150684921)
                    ·
                      refine ⟨3204295407920183363013691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272393877226911150684921 3204295407920183363013691)
                      ·
                        rfl

theorem cell23_6240343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_6240343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240343 prefixEnd_6240343 := by exact prefixLift 6240343
  have htrace : WordTrace (prefixWord ++ tailWord_6240343) baseStart_6240343 baseEnd_6240343 := by
    simpa [prefixWord, tailWord_6240343, baseEnd_6240343] using wordTrace_append hprefix tailTrace_6240343
  have hstable : (prefixWord ++ tailWord_6240343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240343).length < 2 ^ (prefixWord ++ tailWord_6240343).sum := by decide
  have hdescent : baseEnd_6240343 < baseStart_6240343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240394 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6240394 : Nat := 118140960795 + 6240394 * 2 ^ 59
def prefixEnd_6240394 : Nat := 4983230072969 + 3 ^ 40 * 6240394 * 2
def baseEnd_6240394 : Nat := 3204321595433562663475957

theorem tailTrace_6240394 : CollatzResearch.WordTrace tailWord_6240394 prefixEnd_6240394 3204321595433562663475957 := by
  unfold tailWord_6240394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56901466938531446822418059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151737245169417191526448157 56901466938531446822418059)
  ·
    refine ⟨85352200407797170233627089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56901466938531446822418059 85352200407797170233627089)
    ·
      refine ⟨64014150305847877675220317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85352200407797170233627089 64014150305847877675220317)
      ·
        refine ⟨24005306364692954128207619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64014150305847877675220317 24005306364692954128207619)
        ·
          refine ⟨36007959547039431192311429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24005306364692954128207619 36007959547039431192311429)
          ·
            refine ⟨6751492415069893348558393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36007959547039431192311429 6751492415069893348558393)
            ·
              refine ⟨5063619311302420011418795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751492415069893348558393 5063619311302420011418795)
              ·
                refine ⟨7595428966953630017128193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5063619311302420011418795 7595428966953630017128193)
                ·
                  refine ⟨5696571725215222512846145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7595428966953630017128193 5696571725215222512846145)
                  ·
                    refine ⟨4272428793911416884634609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5696571725215222512846145 4272428793911416884634609)
                    ·
                      refine ⟨3204321595433562663475957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272428793911416884634609 3204321595433562663475957)
                      ·
                        rfl

theorem cell23_6240394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6240394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240394 prefixEnd_6240394 := by exact prefixLift 6240394
  have htrace : WordTrace (prefixWord ++ tailWord_6240394) baseStart_6240394 baseEnd_6240394 := by
    simpa [prefixWord, tailWord_6240394, baseEnd_6240394] using wordTrace_append hprefix tailTrace_6240394
  have hstable : (prefixWord ++ tailWord_6240394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240394).length < 2 ^ (prefixWord ++ tailWord_6240394).sum := by decide
  have hdescent : baseEnd_6240394 < baseStart_6240394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240409 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_6240409 : Nat := 118140960795 + 6240409 * 2 ^ 59
def prefixEnd_6240409 : Nat := 4983230072969 + 3 ^ 40 * 6240409 * 2
def baseEnd_6240409 : Nat := 1068109765881126701596129

theorem tailTrace_6240409 : CollatzResearch.WordTrace tailWord_6240409 prefixEnd_6240409 1068109765881126701596129 := by
  unfold tailWord_6240409
  simp only [CollatzResearch.WordTrace]
  refine ⟨227606414849071444851468281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151737609899380963234312187 227606414849071444851468281)
  ·
    refine ⟨170704811136803583638601211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227606414849071444851468281 170704811136803583638601211)
    ·
      refine ⟨256057216705205375457901817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170704811136803583638601211 256057216705205375457901817)
      ·
        refine ⟨192042912528904031593426363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256057216705205375457901817 192042912528904031593426363)
        ·
          refine ⟨288064368793356047390139545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192042912528904031593426363 288064368793356047390139545)
          ·
            refine ⟨216048276595017035542604659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288064368793356047390139545 216048276595017035542604659)
            ·
              refine ⟨324072414892525553313906989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216048276595017035542604659 324072414892525553313906989)
              ·
                refine ⟨121527155584697082492715121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324072414892525553313906989 121527155584697082492715121)
                ·
                  refine ⟨91145366688522811869536341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121527155584697082492715121 91145366688522811869536341)
                  ·
                    refine ⟨1068109765881126701596129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91145366688522811869536341 1068109765881126701596129)
                    ·
                      rfl

theorem cell23_6240409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_6240409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240409 prefixEnd_6240409 := by exact prefixLift 6240409
  have htrace : WordTrace (prefixWord ++ tailWord_6240409) baseStart_6240409 baseEnd_6240409 := by
    simpa [prefixWord, tailWord_6240409, baseEnd_6240409] using wordTrace_append hprefix tailTrace_6240409
  have hstable : (prefixWord ++ tailWord_6240409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240409).length < 2 ^ (prefixWord ++ tailWord_6240409).sum := by decide
  have hdescent : baseEnd_6240409 < baseStart_6240409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240413 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_6240413 : Nat := 118140960795 + 6240413 * 2 ^ 59
def prefixEnd_6240413 : Nat := 4983230072969 + 3 ^ 40 * 6240413 * 2
def baseEnd_6240413 : Nat := 1068110450521999363046123

theorem tailTrace_6240413 : CollatzResearch.WordTrace tailWord_6240413 prefixEnd_6240413 1068110450521999363046123 := by
  unfold tailWord_6240413
  simp only [CollatzResearch.WordTrace]
  refine ⟨227606560741056953534613893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151737707160704635689742595 227606560741056953534613893)
  ·
    refine ⟨42676230138948178787740105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227606560741056953534613893 42676230138948178787740105)
    ·
      refine ⟨32007172604211134090805079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42676230138948178787740105 32007172604211134090805079)
      ·
        refine ⟨48010758906316701136207619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32007172604211134090805079 48010758906316701136207619)
        ·
          refine ⟨72016138359475051704311429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48010758906316701136207619 72016138359475051704311429)
          ·
            refine ⟨13503025942401572194558393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72016138359475051704311429 13503025942401572194558393)
            ·
              refine ⟨10127269456801179145918795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13503025942401572194558393 10127269456801179145918795)
              ·
                refine ⟨15190904185201768718878193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10127269456801179145918795 15190904185201768718878193)
                ·
                  refine ⟨11393178138901326539158645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15190904185201768718878193 11393178138901326539158645)
                  ·
                    refine ⟨1068110450521999363046123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11393178138901326539158645 1068110450521999363046123)
                    ·
                      rfl

theorem cell23_6240413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_6240413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240413 prefixEnd_6240413 := by exact prefixLift 6240413
  have htrace : WordTrace (prefixWord ++ tailWord_6240413) baseStart_6240413 baseEnd_6240413 := by
    simpa [prefixWord, tailWord_6240413, baseEnd_6240413] using wordTrace_append hprefix tailTrace_6240413
  have hstable : (prefixWord ++ tailWord_6240413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240413).length < 2 ^ (prefixWord ++ tailWord_6240413).sum := by decide
  have hdescent : baseEnd_6240413 < baseStart_6240413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240419 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_6240419 : Nat := 118140960795 + 6240419 * 2 ^ 59
def prefixEnd_6240419 : Nat := 4983230072969 + 3 ^ 40 * 6240419 * 2
def baseEnd_6240419 : Nat := 3204334432449925065663341

theorem tailTrace_6240419 : CollatzResearch.WordTrace tailWord_6240419 prefixEnd_6240419 3204334432449925065663341 := by
  unfold tailWord_6240419
  simp only [CollatzResearch.WordTrace]
  refine ⟨227606779579035216559332311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151737853052690144372888207 227606779579035216559332311)
  ·
    refine ⟨341410169368552824838998467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227606779579035216559332311 341410169368552824838998467)
    ·
      refine ⟨512115254052829237258497701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341410169368552824838998467 512115254052829237258497701)
      ·
        refine ⟨96021610134905481985968319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512115254052829237258497701 96021610134905481985968319)
        ·
          refine ⟨144032415202358222978952479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96021610134905481985968319 144032415202358222978952479)
          ·
            refine ⟨216048622803537334468428719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144032415202358222978952479 216048622803537334468428719)
            ·
              refine ⟨324072934205306001702643079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216048622803537334468428719 324072934205306001702643079)
              ·
                refine ⟨486109401307959002553964619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324072934205306001702643079 486109401307959002553964619)
                ·
                  refine ⟨729164101961938503830946929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486109401307959002553964619 729164101961938503830946929)
                  ·
                    refine ⟨546873076471453877873210197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729164101961938503830946929 546873076471453877873210197)
                    ·
                      refine ⟨3204334432449925065663341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 546873076471453877873210197 3204334432449925065663341)
                      ·
                        rfl

theorem cell23_6240419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_6240419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240419 prefixEnd_6240419 := by exact prefixLift 6240419
  have htrace : WordTrace (prefixWord ++ tailWord_6240419) baseStart_6240419 baseEnd_6240419 := by
    simpa [prefixWord, tailWord_6240419, baseEnd_6240419] using wordTrace_append hprefix tailTrace_6240419
  have hstable : (prefixWord ++ tailWord_6240419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240419).length < 2 ^ (prefixWord ++ tailWord_6240419).sum := by decide
  have hdescent : baseEnd_6240419 < baseStart_6240419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240477 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6240477 : Nat := 118140960795 + 6240477 * 2 ^ 59
def prefixEnd_6240477 : Nat := 4983230072969 + 3 ^ 40 * 6240477 * 2
def baseEnd_6240477 : Nat := 1068121404775961946246025

theorem tailTrace_6240477 : CollatzResearch.WordTrace tailWord_6240477 prefixEnd_6240477 1068121404775961946246025 := by
  unfold tailWord_6240477
  simp only [CollatzResearch.WordTrace]
  refine ⟨227608895012825092464943685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151739263341883394976629123 227608895012825092464943685)
  ·
    refine ⟨42676667814904704837176941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227608895012825092464943685 42676667814904704837176941)
    ·
      refine ⟨16003750430589264313941353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42676667814904704837176941 16003750430589264313941353)
      ·
        refine ⟨12002812822941948235456015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16003750430589264313941353 12002812822941948235456015)
        ·
          refine ⟨18004219234412922353184023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002812822941948235456015 18004219234412922353184023)
          ·
            refine ⟨27006328851619383529776035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18004219234412922353184023 27006328851619383529776035)
            ·
              refine ⟨40509493277429075294664053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27006328851619383529776035 40509493277429075294664053)
              ·
                refine ⟨3797764994758975808874755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40509493277429075294664053 3797764994758975808874755)
                ·
                  refine ⟨5696647492138463713312133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797764994758975808874755 5696647492138463713312133)
                  ·
                    refine ⟨1068121404775961946246025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696647492138463713312133 1068121404775961946246025)
                    ·
                      rfl

theorem cell23_6240477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6240477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240477 prefixEnd_6240477 := by exact prefixLift 6240477
  have htrace : WordTrace (prefixWord ++ tailWord_6240477) baseStart_6240477 baseEnd_6240477 := by
    simpa [prefixWord, tailWord_6240477, baseEnd_6240477] using wordTrace_append hprefix tailTrace_6240477
  have hstable : (prefixWord ++ tailWord_6240477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240477).length < 2 ^ (prefixWord ++ tailWord_6240477).sum := by decide
  have hdescent : baseEnd_6240477 < baseStart_6240477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240510 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_6240510 : Nat := 118140960795 + 6240510 * 2 ^ 59
def prefixEnd_6240510 : Nat := 4983230072969 + 3 ^ 40 * 6240510 * 2
def baseEnd_6240510 : Nat := 3204381159189484209625423

theorem tailTrace_6240510 : CollatzResearch.WordTrace tailWord_6240510 prefixEnd_6240510 3204381159189484209625423 := by
  unfold tailWord_6240510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451262327713192387611873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151740065747803692733929989 28451262327713192387611873)
  ·
    refine ⟨21338446745784894290708905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28451262327713192387611873 21338446745784894290708905)
    ·
      refine ⟨16003835059338670718031679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21338446745784894290708905 16003835059338670718031679)
      ·
        refine ⟨24005752589008006077047519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16003835059338670718031679 24005752589008006077047519)
        ·
          refine ⟨36008628883512009115571279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24005752589008006077047519 36008628883512009115571279)
          ·
            refine ⟨54012943325268013673356919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36008628883512009115571279 54012943325268013673356919)
            ·
              refine ⟨81019414987902020510035379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54012943325268013673356919 81019414987902020510035379)
              ·
                refine ⟨121529122481853030765053069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81019414987902020510035379 121529122481853030765053069)
                ·
                  refine ⟨45573420930694886536894901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121529122481853030765053069 45573420930694886536894901)
                  ·
                    refine ⟨4272508212252645612833897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45573420930694886536894901 4272508212252645612833897)
                    ·
                      refine ⟨3204381159189484209625423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272508212252645612833897 3204381159189484209625423)
                      ·
                        rfl

theorem cell23_6240510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_6240510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240510 prefixEnd_6240510 := by exact prefixLift 6240510
  have htrace : WordTrace (prefixWord ++ tailWord_6240510) baseStart_6240510 baseEnd_6240510 := by
    simpa [prefixWord, tailWord_6240510, baseEnd_6240510] using wordTrace_append hprefix tailTrace_6240510
  have hstable : (prefixWord ++ tailWord_6240510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240510).length < 2 ^ (prefixWord ++ tailWord_6240510).sum := by decide
  have hdescent : baseEnd_6240510 < baseStart_6240510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240520 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_6240520 : Nat := 118140960795 + 6240520 * 2 ^ 59
def prefixEnd_6240520 : Nat := 4983230072969 + 3 ^ 40 * 6240520 * 2
def baseEnd_6240520 : Nat := 1068128764665343056833459

theorem tailTrace_6240520 : CollatzResearch.WordTrace tailWord_6240520 prefixEnd_6240520 1068128764665343056833459 := by
  unfold tailWord_6240520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113805231675834655404379507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151740308901112873872506009 113805231675834655404379507)
  ·
    refine ⟨170707847513751983106569261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113805231675834655404379507 170707847513751983106569261)
    ·
      refine ⟨64015442817656993664963473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170707847513751983106569261 64015442817656993664963473)
      ·
        refine ⟨48011582113242745248722605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64015442817656993664963473 48011582113242745248722605)
        ·
          refine ⟨18004343292466029468270977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48011582113242745248722605 18004343292466029468270977)
          ·
            refine ⟨13503257469349522101203233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18004343292466029468270977 13503257469349522101203233)
            ·
              refine ⟨10127443102012141575902425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13503257469349522101203233 10127443102012141575902425)
              ·
                refine ⟨7595582326509106181926819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10127443102012141575902425 7595582326509106181926819)
                ·
                  refine ⟨11393373489763659272890229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7595582326509106181926819 11393373489763659272890229)
                  ·
                    refine ⟨1068128764665343056833459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11393373489763659272890229 1068128764665343056833459)
                    ·
                      rfl

theorem cell23_6240520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_6240520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240520 prefixEnd_6240520 := by exact prefixLift 6240520
  have htrace : WordTrace (prefixWord ++ tailWord_6240520) baseStart_6240520 baseEnd_6240520 := by
    simpa [prefixWord, tailWord_6240520, baseEnd_6240520] using wordTrace_append hprefix tailTrace_6240520
  have hstable : (prefixWord ++ tailWord_6240520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240520).length < 2 ^ (prefixWord ++ tailWord_6240520).sum := by decide
  have hdescent : baseEnd_6240520 < baseStart_6240520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240523 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 6, 2]
def baseStart_6240523 : Nat := 118140960795 + 6240523 * 2 ^ 59
def prefixEnd_6240523 : Nat := 4983230072969 + 3 ^ 40 * 6240523 * 2
def baseEnd_6240523 : Nat := 3204387834437992658762863

theorem tailTrace_6240523 : CollatzResearch.WordTrace tailWord_6240523 prefixEnd_6240523 3204387834437992658762863 := by
  unfold tailWord_6240523
  simp only [CollatzResearch.WordTrace]
  refine ⟨227610572770658442321118223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151740381847105628214078815 227610572770658442321118223)
  ·
    refine ⟨341415859155987663481677335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227610572770658442321118223 341415859155987663481677335)
    ·
      refine ⟨512123788733981495222516003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341415859155987663481677335 512123788733981495222516003)
      ·
        refine ⟨768185683100972242833774005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512123788733981495222516003 768185683100972242833774005)
        ·
          refine ⟨72017407790716147765666313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 768185683100972242833774005 72017407790716147765666313)
          ·
            refine ⟨54013055843037110824249735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72017407790716147765666313 54013055843037110824249735)
            ·
              refine ⟨81019583764555666236374603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54013055843037110824249735 81019583764555666236374603)
              ·
                refine ⟨121529375646833499354561905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81019583764555666236374603 121529375646833499354561905)
                ·
                  refine ⟨91147031735125124515921429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121529375646833499354561905 91147031735125124515921429)
                  ·
                    refine ⟨4272517112583990211683817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91147031735125124515921429 4272517112583990211683817)
                    ·
                      refine ⟨3204387834437992658762863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272517112583990211683817 3204387834437992658762863)
                      ·
                        rfl

theorem cell23_6240523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6, 2].length) (baseStart_6240523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240523 prefixEnd_6240523 := by exact prefixLift 6240523
  have htrace : WordTrace (prefixWord ++ tailWord_6240523) baseStart_6240523 baseEnd_6240523 := by
    simpa [prefixWord, tailWord_6240523, baseEnd_6240523] using wordTrace_append hprefix tailTrace_6240523
  have hstable : (prefixWord ++ tailWord_6240523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240523).length < 2 ^ (prefixWord ++ tailWord_6240523).sum := by decide
  have hdescent : baseEnd_6240523 < baseStart_6240523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240533 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_6240533 : Nat := 118140960795 + 6240533 * 2 ^ 59
def prefixEnd_6240533 : Nat := 4983230072969 + 3 ^ 40 * 6240533 * 2
def baseEnd_6240533 : Nat := 1068130989748179206545939

theorem tailTrace_6240533 : CollatzResearch.WordTrace tailWord_6240533 prefixEnd_6240533 1068130989748179206545939 := by
  unfold tailWord_6240533
  simp only [CollatzResearch.WordTrace]
  refine ⟨227610937500622214028982253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151740625000414809352654835 227610937500622214028982253)
  ·
    refine ⟨85354101562733330260868345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227610937500622214028982253 85354101562733330260868345)
    ·
      refine ⟨64015576172049997695651259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85354101562733330260868345 64015576172049997695651259)
      ·
        refine ⟨96023364258074996543476889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64015576172049997695651259 96023364258074996543476889)
        ·
          refine ⟨72017523193556247407607667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96023364258074996543476889 72017523193556247407607667)
          ·
            refine ⟨108026284790334371111411501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72017523193556247407607667 108026284790334371111411501)
            ·
              refine ⟨40509856796375389166779313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108026284790334371111411501 40509856796375389166779313)
              ·
                refine ⟨30382392597281541875084485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40509856796375389166779313 30382392597281541875084485)
                ·
                  refine ⟨5696698611990289101578341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30382392597281541875084485 5696698611990289101578341)
                  ·
                    refine ⟨1068130989748179206545939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696698611990289101578341 1068130989748179206545939)
                    ·
                      rfl

theorem cell23_6240533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_6240533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240533 prefixEnd_6240533 := by exact prefixLift 6240533
  have htrace : WordTrace (prefixWord ++ tailWord_6240533) baseStart_6240533 baseEnd_6240533 := by
    simpa [prefixWord, tailWord_6240533, baseEnd_6240533] using wordTrace_append hprefix tailTrace_6240533
  have hstable : (prefixWord ++ tailWord_6240533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240533).length < 2 ^ (prefixWord ++ tailWord_6240533).sum := by decide
  have hdescent : baseEnd_6240533 < baseStart_6240533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240543 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_6240543 : Nat := 118140960795 + 6240543 * 2 ^ 59
def prefixEnd_6240543 : Nat := 4983230072969 + 3 ^ 40 * 6240543 * 2
def baseEnd_6240543 : Nat := 3204398104051082580512771

theorem tailTrace_6240543 : CollatzResearch.WordTrace tailWord_6240543 prefixEnd_6240543 3204398104051082580512771 := by
  unfold tailWord_6240543
  simp only [CollatzResearch.WordTrace]
  refine ⟨227611302230585985736846283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151740868153723990491230855 227611302230585985736846283)
  ·
    refine ⟨341416953345878978605269425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227611302230585985736846283 341416953345878978605269425)
    ·
      refine ⟨256062715009409233953952069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341416953345878978605269425 256062715009409233953952069)
      ·
        refine ⟨48011759064264231366366013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256062715009409233953952069 48011759064264231366366013)
        ·
          refine ⟨18004409649099086762387255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48011759064264231366366013 18004409649099086762387255)
          ·
            refine ⟨27006614473648630143580883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18004409649099086762387255 27006614473648630143580883)
            ·
              refine ⟨40509921710472945215371325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27006614473648630143580883 40509921710472945215371325)
              ·
                refine ⟨15191220641427354455764247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40509921710472945215371325 15191220641427354455764247)
                ·
                  refine ⟨22786830962141031683646371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15191220641427354455764247 22786830962141031683646371)
                  ·
                    refine ⟨34180246443211547525469557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22786830962141031683646371 34180246443211547525469557)
                    ·
                      refine ⟨3204398104051082580512771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34180246443211547525469557 3204398104051082580512771)
                      ·
                        rfl

theorem cell23_6240543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_6240543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240543 prefixEnd_6240543 := by exact prefixLift 6240543
  have htrace : WordTrace (prefixWord ++ tailWord_6240543) baseStart_6240543 baseEnd_6240543 := by
    simpa [prefixWord, tailWord_6240543, baseEnd_6240543] using wordTrace_append hprefix tailTrace_6240543
  have hstable : (prefixWord ++ tailWord_6240543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240543).length < 2 ^ (prefixWord ++ tailWord_6240543).sum := by decide
  have hdescent : baseEnd_6240543 < baseStart_6240543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240576 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_6240576 : Nat := 118140960795 + 6240576 * 2 ^ 59
def prefixEnd_6240576 : Nat := 4983230072969 + 3 ^ 40 * 6240576 * 2
def baseEnd_6240576 : Nat := 1068138349637560317133373

theorem tailTrace_6240576 : CollatzResearch.WordTrace tailWord_6240576 prefixEnd_6240576 1068138349637560317133373 := by
  unfold tailWord_6240576
  simp only [CollatzResearch.WordTrace]
  refine ⟨113806252919733216186398791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151741670559644288248531721 113806252919733216186398791)
  ·
    refine ⟨170709379379599824279598187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113806252919733216186398791 170709379379599824279598187)
    ·
      refine ⟨256064069069399736419397281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170709379379599824279598187 256064069069399736419397281)
      ·
        refine ⟨192048051802049802314547961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256064069069399736419397281 192048051802049802314547961)
        ·
          refine ⟨144036038851537351735910971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192048051802049802314547961 144036038851537351735910971)
          ·
            refine ⟨216054058277306027603866457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144036038851537351735910971 216054058277306027603866457)
            ·
              refine ⟨162040543707979520702899843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216054058277306027603866457 162040543707979520702899843)
              ·
                refine ⟨243060815561969281054349765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162040543707979520702899843 243060815561969281054349765)
                ·
                  refine ⟨45573902917869240197690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243060815561969281054349765 45573902917869240197690581)
                  ·
                    refine ⟨1068138349637560317133373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45573902917869240197690581 1068138349637560317133373)
                    ·
                      rfl

theorem cell23_6240576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_6240576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240576 prefixEnd_6240576 := by exact prefixLift 6240576
  have htrace : WordTrace (prefixWord ++ tailWord_6240576) baseStart_6240576 baseEnd_6240576 := by
    simpa [prefixWord, tailWord_6240576, baseEnd_6240576] using wordTrace_append hprefix tailTrace_6240576
  have hstable : (prefixWord ++ tailWord_6240576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240576).length < 2 ^ (prefixWord ++ tailWord_6240576).sum := by decide
  have hdescent : baseEnd_6240576 < baseStart_6240576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240577 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6240577 : Nat := 118140960795 + 6240577 * 2 ^ 59
def prefixEnd_6240577 : Nat := 4983230072969 + 3 ^ 40 * 6240577 * 2
def baseEnd_6240577 : Nat := 3204415562393335447487615

theorem tailTrace_6240577 : CollatzResearch.WordTrace tailWord_6240577 prefixEnd_6240577 3204415562393335447487615 := by
  unfold tailWord_6240577
  simp only [CollatzResearch.WordTrace]
  refine ⟨227612542312462809543583985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151741694874975206362389323 227612542312462809543583985)
  ·
    refine ⟨170709406734347107157687989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227612542312462809543583985 170709406734347107157687989)
    ·
      refine ⟨16004006881345041296033249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170709406734347107157687989 16004006881345041296033249)
      ·
        refine ⟨12003005161008780972024937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16004006881345041296033249 12003005161008780972024937)
        ·
          refine ⟨9002253870756585729018703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12003005161008780972024937 9002253870756585729018703)
          ·
            refine ⟨13503380806134878593528055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002253870756585729018703 13503380806134878593528055)
            ·
              refine ⟨20255071209202317890292083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503380806134878593528055 20255071209202317890292083)
              ·
                refine ⟨30382606813803476835438125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20255071209202317890292083 30382606813803476835438125)
                ·
                  refine ⟨11393477555176303813289297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30382606813803476835438125 11393477555176303813289297)
                  ·
                    refine ⟨8545108166382227859966973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11393477555176303813289297 8545108166382227859966973)
                    ·
                      refine ⟨3204415562393335447487615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545108166382227859966973 3204415562393335447487615)
                      ·
                        rfl

theorem cell23_6240577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6240577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240577 prefixEnd_6240577 := by exact prefixLift 6240577
  have htrace : WordTrace (prefixWord ++ tailWord_6240577) baseStart_6240577 baseEnd_6240577 := by
    simpa [prefixWord, tailWord_6240577, baseEnd_6240577] using wordTrace_append hprefix tailTrace_6240577
  have hstable : (prefixWord ++ tailWord_6240577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240577).length < 2 ^ (prefixWord ++ tailWord_6240577).sum := by decide
  have hdescent : baseEnd_6240577 < baseStart_6240577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240590 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_6240590 : Nat := 118140960795 + 6240590 * 2 ^ 59
def prefixEnd_6240590 : Nat := 4983230072969 + 3 ^ 40 * 6240590 * 2
def baseEnd_6240590 : Nat := 3204422237641843896625055

theorem tailTrace_6240590 : CollatzResearch.WordTrace tailWord_6240590 prefixEnd_6240590 3204422237641843896625055 := by
  unfold tailWord_6240590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451627057676964095475903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151742010974277141842538149 28451627057676964095475903)
  ·
    refine ⟨42677440586515446143213855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28451627057676964095475903 42677440586515446143213855)
    ·
      refine ⟨64016160879773169214820783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42677440586515446143213855 64016160879773169214820783)
      ·
        refine ⟨96024241319659753822231175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64016160879773169214820783 96024241319659753822231175)
        ·
          refine ⟨144036361979489630733346763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96024241319659753822231175 144036361979489630733346763)
          ·
            refine ⟨216054542969234446100020145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144036361979489630733346763 216054542969234446100020145)
            ·
              refine ⟨162040907226925834575015109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216054542969234446100020145 162040907226925834575015109)
              ·
                refine ⟨30382670105048593982815333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162040907226925834575015109 30382670105048593982815333)
                ·
                  refine ⟨5696750644696611371777875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30382670105048593982815333 5696750644696611371777875)
                  ·
                    refine ⟨8545125967044917057666813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696750644696611371777875 8545125967044917057666813)
                    ·
                      refine ⟨3204422237641843896625055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545125967044917057666813 3204422237641843896625055)
                      ·
                        rfl

theorem cell23_6240590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_6240590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240590 prefixEnd_6240590 := by exact prefixLift 6240590
  have htrace : WordTrace (prefixWord ++ tailWord_6240590) baseStart_6240590 baseEnd_6240590 := by
    simpa [prefixWord, tailWord_6240590, baseEnd_6240590] using wordTrace_append hprefix tailTrace_6240590
  have hstable : (prefixWord ++ tailWord_6240590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240590).length < 2 ^ (prefixWord ++ tailWord_6240590).sum := by decide
  have hdescent : baseEnd_6240590 < baseStart_6240590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240608 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 1, 2, 2]
def baseStart_6240608 : Nat := 118140960795 + 6240608 * 2 ^ 59
def prefixEnd_6240608 : Nat := 4983230072969 + 3 ^ 40 * 6240608 * 2
def baseEnd_6240608 : Nat := 3204431480293624826199973

theorem tailTrace_6240608 : CollatzResearch.WordTrace tailWord_6240608 prefixEnd_6240608 3204431480293624826199973 := by
  unfold tailWord_6240608
  simp only [CollatzResearch.WordTrace]
  refine ⟨113806836487675250918981239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151742448650233667891974985 113806836487675250918981239)
  ·
    refine ⟨170710254731512876378471859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113806836487675250918981239 170710254731512876378471859)
    ·
      refine ⟨256065382097269314567707789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170710254731512876378471859 256065382097269314567707789)
      ·
        refine ⟨96024518286475992962890421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256065382097269314567707789 96024518286475992962890421)
        ·
          refine ⟨9002298589357124340270977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96024518286475992962890421 9002298589357124340270977)
          ·
            refine ⟨6751723942017843255203233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002298589357124340270977 6751723942017843255203233)
            ·
              refine ⟨5063792956513382441402425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751723942017843255203233 5063792956513382441402425)
              ·
                refine ⟨3797844717385036831051819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5063792956513382441402425 3797844717385036831051819)
                ·
                  refine ⟨5696767076077555246577729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797844717385036831051819 5696767076077555246577729)
                  ·
                    refine ⟨4272575307058166434933297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5696767076077555246577729 4272575307058166434933297)
                    ·
                      refine ⟨3204431480293624826199973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272575307058166434933297 3204431480293624826199973)
                      ·
                        rfl

theorem cell23_6240608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_6240608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240608 prefixEnd_6240608 := by exact prefixLift 6240608
  have htrace : WordTrace (prefixWord ++ tailWord_6240608) baseStart_6240608 baseEnd_6240608 := by
    simpa [prefixWord, tailWord_6240608, baseEnd_6240608] using wordTrace_append hprefix tailTrace_6240608
  have hstable : (prefixWord ++ tailWord_6240608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240608).length < 2 ^ (prefixWord ++ tailWord_6240608).sum := by decide
  have hdescent : baseEnd_6240608 < baseStart_6240608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240613 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6240613 : Nat := 118140960795 + 6240613 * 2 ^ 59
def prefixEnd_6240613 : Nat := 4983230072969 + 3 ^ 40 * 6240613 * 2
def baseEnd_6240613 : Nat := 3204434047696897306637449

theorem tailTrace_6240613 : CollatzResearch.WordTrace tailWord_6240613 prefixEnd_6240613 3204434047696897306637449 := by
  unfold tailWord_6240613
  simp only [CollatzResearch.WordTrace]
  refine ⟨227613855340332387691894493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151742570226888258461262995 227613855340332387691894493)
  ·
    refine ⟨85355195752624645384460435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227613855340332387691894493 85355195752624645384460435)
    ·
      refine ⟨128032793628936968076690653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85355195752624645384460435 128032793628936968076690653)
      ·
        refine ⟨48012297610851363028758995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128032793628936968076690653 48012297610851363028758995)
        ·
          refine ⟨72018446416277044543138493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48012297610851363028758995 72018446416277044543138493)
          ·
            refine ⟨27006917406103891703676935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72018446416277044543138493 27006917406103891703676935)
            ·
              refine ⟨40510376109155837555515403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27006917406103891703676935 40510376109155837555515403)
              ·
                refine ⟨60765564163733756333273105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40510376109155837555515403 60765564163733756333273105)
                ·
                  refine ⟨45574173122800317249954829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60765564163733756333273105 45574173122800317249954829)
                  ·
                    refine ⟨17090314921050118968733061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45574173122800317249954829 17090314921050118968733061)
                    ·
                      refine ⟨3204434047696897306637449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17090314921050118968733061 3204434047696897306637449)
                      ·
                        rfl

theorem cell23_6240613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6240613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240613 prefixEnd_6240613 := by exact prefixLift 6240613
  have htrace : WordTrace (prefixWord ++ tailWord_6240613) baseStart_6240613 baseEnd_6240613 := by
    simpa [prefixWord, tailWord_6240613, baseEnd_6240613] using wordTrace_append hprefix tailTrace_6240613
  have hstable : (prefixWord ++ tailWord_6240613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240613).length < 2 ^ (prefixWord ++ tailWord_6240613).sum := by decide
  have hdescent : baseEnd_6240613 < baseStart_6240613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240633 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_6240633 : Nat := 118140960795 + 6240633 * 2 ^ 59
def prefixEnd_6240633 : Nat := 4983230072969 + 3 ^ 40 * 6240633 * 2
def baseEnd_6240633 : Nat := 3204444317309987228387357

theorem tailTrace_6240633 : CollatzResearch.WordTrace tailWord_6240633 prefixEnd_6240633 3204444317309987228387357 := by
  unfold tailWord_6240633
  simp only [CollatzResearch.WordTrace]
  refine ⟨227614584800259931107622553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151743056533506620738415035 227614584800259931107622553)
  ·
    refine ⟨170710938600194948330716915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227614584800259931107622553 170710938600194948330716915)
    ·
      refine ⟨256066407900292422496075373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170710938600194948330716915 256066407900292422496075373)
      ·
        refine ⟨96024902962609658436028265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256066407900292422496075373 96024902962609658436028265)
        ·
          refine ⟨72018677221957243827021199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96024902962609658436028265 72018677221957243827021199)
          ·
            refine ⟨108028015832935865740531799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72018677221957243827021199 108028015832935865740531799)
            ·
              refine ⟨162042023749403798610797699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108028015832935865740531799 162042023749403798610797699)
              ·
                refine ⟨243063035624105697916196549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162042023749403798610797699 243063035624105697916196549)
                ·
                  refine ⟨45574319179519818359286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243063035624105697916196549 45574319179519818359286853)
                  ·
                    refine ⟨8545184846159965942366285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45574319179519818359286853 8545184846159965942366285)
                    ·
                      refine ⟨3204444317309987228387357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545184846159965942366285 3204444317309987228387357)
                      ·
                        rfl

theorem cell23_6240633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_6240633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240633 prefixEnd_6240633 := by exact prefixLift 6240633
  have htrace : WordTrace (prefixWord ++ tailWord_6240633) baseStart_6240633 baseEnd_6240633 := by
    simpa [prefixWord, tailWord_6240633, baseEnd_6240633] using wordTrace_append hprefix tailTrace_6240633
  have hstable : (prefixWord ++ tailWord_6240633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240633).length < 2 ^ (prefixWord ++ tailWord_6240633).sum := by decide
  have hdescent : baseEnd_6240633 < baseStart_6240633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240647 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_6240647 : Nat := 118140960795 + 6240647 * 2 ^ 59
def prefixEnd_6240647 : Nat := 4983230072969 + 3 ^ 40 * 6240647 * 2
def baseEnd_6240647 : Nat := 3204451506039150173612293

theorem tailTrace_6240647 : CollatzResearch.WordTrace tailWord_6240647 prefixEnd_6240647 3204451506039150173612293 := by
  unfold tailWord_6240647
  simp only [CollatzResearch.WordTrace]
  refine ⟨227615095422209211498632195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151743396948139474332421463 227615095422209211498632195)
  ·
    refine ⟨341422643133313817247948293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227615095422209211498632195 341422643133313817247948293)
    ·
      refine ⟨64016745587496340733990305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341422643133313817247948293 64016745587496340733990305)
      ·
        refine ⟨48012559190622255550492729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64016745587496340733990305 48012559190622255550492729)
        ·
          refine ⟨36009419392966691662869547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48012559190622255550492729 36009419392966691662869547)
          ·
            refine ⟨54014129089450037494304321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36009419392966691662869547 54014129089450037494304321)
            ·
              refine ⟨40510596817087528120728241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54014129089450037494304321 40510596817087528120728241)
              ·
                refine ⟨30382947612815646090546181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40510596817087528120728241 30382947612815646090546181)
                ·
                  refine ⟨5696802677402933641977409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30382947612815646090546181 5696802677402933641977409)
                  ·
                    refine ⟨4272602008052200231483057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5696802677402933641977409 4272602008052200231483057)
                    ·
                      refine ⟨3204451506039150173612293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272602008052200231483057 3204451506039150173612293)
                      ·
                        rfl

theorem cell23_6240647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_6240647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240647 prefixEnd_6240647 := by exact prefixLift 6240647
  have htrace : WordTrace (prefixWord ++ tailWord_6240647) baseStart_6240647 baseEnd_6240647 := by
    simpa [prefixWord, tailWord_6240647, baseEnd_6240647] using wordTrace_append hprefix tailTrace_6240647
  have hstable : (prefixWord ++ tailWord_6240647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240647).length < 2 ^ (prefixWord ++ tailWord_6240647).sum := by decide
  have hdescent : baseEnd_6240647 < baseStart_6240647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240664 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6240664 : Nat := 118140960795 + 6240664 * 2 ^ 59
def prefixEnd_6240664 : Nat := 4983230072969 + 3 ^ 40 * 6240664 * 2
def baseEnd_6240664 : Nat := 3204460235210276607099715

theorem tailTrace_6240664 : CollatzResearch.WordTrace tailWord_6240664 prefixEnd_6240664 3204460235210276607099715 := by
  unfold tailWord_6240664
  simp only [CollatzResearch.WordTrace]
  refine ⟨113807857731573811701000523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151743810308765082268000697 113807857731573811701000523)
  ·
    refine ⟨170711786597360717551500785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113807857731573811701000523 170711786597360717551500785)
    ·
      refine ⟨128033839948020538163625589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170711786597360717551500785 128033839948020538163625589)
      ·
        refine ⟨12003172495126925452839899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128033839948020538163625589 12003172495126925452839899)
        ·
          refine ⟨18004758742690388179259849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003172495126925452839899 18004758742690388179259849)
          ·
            refine ⟨13503569057017791134444887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18004758742690388179259849 13503569057017791134444887)
            ·
              refine ⟨20255353585526686701667331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503569057017791134444887 20255353585526686701667331)
              ·
                refine ⟨30383030378290030052500997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20255353585526686701667331 30383030378290030052500997)
                ·
                  refine ⟨5696818195929380634843937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30383030378290030052500997 5696818195929380634843937)
                  ·
                    refine ⟨4272613646947035476132953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5696818195929380634843937 4272613646947035476132953)
                    ·
                      refine ⟨3204460235210276607099715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272613646947035476132953 3204460235210276607099715)
                      ·
                        rfl

theorem cell23_6240664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6240664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240664 prefixEnd_6240664 := by exact prefixLift 6240664
  have htrace : WordTrace (prefixWord ++ tailWord_6240664) baseStart_6240664 baseEnd_6240664 := by
    simpa [prefixWord, tailWord_6240664, baseEnd_6240664] using wordTrace_append hprefix tailTrace_6240664
  have hstable : (prefixWord ++ tailWord_6240664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240664).length < 2 ^ (prefixWord ++ tailWord_6240664).sum := by decide
  have hdescent : baseEnd_6240664 < baseStart_6240664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240700 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_6240700 : Nat := 118140960795 + 6240700 * 2 ^ 59
def prefixEnd_6240700 : Nat := 4983230072969 + 3 ^ 40 * 6240700 * 2
def baseEnd_6240700 : Nat := 1068159573504612822083183

theorem tailTrace_6240700 : CollatzResearch.WordTrace tailWord_6240700 prefixEnd_6240700 1068159573504612822083183 := by
  unfold tailWord_6240700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113808514245508600775155777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151744685660678134366874369 113808514245508600775155777)
  ·
    refine ⟨85356385684131450581366833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113808514245508600775155777 85356385684131450581366833)
    ·
      refine ⟨64017289263098587936025125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85356385684131450581366833 64017289263098587936025125)
      ·
        refine ⟨12003241736830985238004711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64017289263098587936025125 12003241736830985238004711)
        ·
          refine ⟨18004862605246477857007067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003241736830985238004711 18004862605246477857007067)
          ·
            refine ⟨27007293907869716785510601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18004862605246477857007067 27007293907869716785510601)
            ·
              refine ⟨20255470430902287589132951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27007293907869716785510601 20255470430902287589132951)
              ·
                refine ⟨30383205646353431383699427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20255470430902287589132951 30383205646353431383699427)
                ·
                  refine ⟨45574808469530147075549141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30383205646353431383699427 45574808469530147075549141)
                  ·
                    refine ⟨1068159573504612822083183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45574808469530147075549141 1068159573504612822083183)
                    ·
                      rfl

theorem cell23_6240700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_6240700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240700 prefixEnd_6240700 := by exact prefixLift 6240700
  have htrace : WordTrace (prefixWord ++ tailWord_6240700) baseStart_6240700 baseEnd_6240700 := by
    simpa [prefixWord, tailWord_6240700, baseEnd_6240700] using wordTrace_append hprefix tailTrace_6240700
  have hstable : (prefixWord ++ tailWord_6240700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240700).length < 2 ^ (prefixWord ++ tailWord_6240700).sum := by decide
  have hdescent : baseEnd_6240700 < baseStart_6240700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240754 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6240754 : Nat := 118140960795 + 6240754 * 2 ^ 59
def prefixEnd_6240754 : Nat := 4983230072969 + 3 ^ 40 * 6240754 * 2
def baseEnd_6240754 : Nat := 3204506448469181254974301

theorem tailTrace_6240754 : CollatzResearch.WordTrace tailWord_6240754 prefixEnd_6240754 3204506448469181254974301 := by
  unfold tailWord_6240754
  simp only [CollatzResearch.WordTrace]
  refine ⟨56904749508205392193194329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151745998688547712515184877 56904749508205392193194329)
  ·
    refine ⟨42678562131154044144895747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56904749508205392193194329 42678562131154044144895747)
    ·
      refine ⟨64017843196731066217343621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42678562131154044144895747 64017843196731066217343621)
      ·
        refine ⟨12003345599387074915751929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64017843196731066217343621 12003345599387074915751929)
        ·
          refine ⟨9002509199540306186813947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12003345599387074915751929 9002509199540306186813947)
          ·
            refine ⟨13503763799310459280220921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002509199540306186813947 13503763799310459280220921)
            ·
              refine ⟨10127822849482844460165691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13503763799310459280220921 10127822849482844460165691)
              ·
                refine ⟨15191734274224266690248537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10127822849482844460165691 15191734274224266690248537)
                ·
                  refine ⟨11393800705668200017686403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15191734274224266690248537 11393800705668200017686403)
                  ·
                    refine ⟨17090701058502300026529605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11393800705668200017686403 17090701058502300026529605)
                    ·
                      refine ⟨3204506448469181254974301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17090701058502300026529605 3204506448469181254974301)
                      ·
                        rfl

theorem cell23_6240754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6240754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240754 prefixEnd_6240754 := by exact prefixLift 6240754
  have htrace : WordTrace (prefixWord ++ tailWord_6240754) baseStart_6240754 baseEnd_6240754 := by
    simpa [prefixWord, tailWord_6240754, baseEnd_6240754] using wordTrace_append hprefix tailTrace_6240754
  have hstable : (prefixWord ++ tailWord_6240754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240754).length < 2 ^ (prefixWord ++ tailWord_6240754).sum := by decide
  have hdescent : baseEnd_6240754 < baseStart_6240754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240783 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_6240783 : Nat := 118140960795 + 6240783 * 2 ^ 59
def prefixEnd_6240783 : Nat := 4983230072969 + 3 ^ 40 * 6240783 * 2
def baseEnd_6240783 : Nat := 3204521339408161641511667

theorem tailTrace_6240783 : CollatzResearch.WordTrace tailWord_6240783 prefixEnd_6240783 3204521339408161641511667 := by
  unfold tailWord_6240783
  simp only [CollatzResearch.WordTrace]
  refine ⟨227620055749716506725583003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151746703833144337817055335 227620055749716506725583003)
  ·
    refine ⟨341430083624574760088374505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227620055749716506725583003 341430083624574760088374505)
    ·
      refine ⟨256072562718431070066280879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341430083624574760088374505 256072562718431070066280879)
      ·
        refine ⟨384108844077646605099421319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256072562718431070066280879 384108844077646605099421319)
        ·
          refine ⟨576163266116469907649131979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384108844077646605099421319 576163266116469907649131979)
          ·
            refine ⟨864244899174704861473697969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576163266116469907649131979 864244899174704861473697969)
            ·
              refine ⟨648183674381028646105273477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864244899174704861473697969 648183674381028646105273477)
              ·
                refine ⟨121534438946442871144738777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648183674381028646105273477 121534438946442871144738777)
                ·
                  refine ⟨91150829209832153358554083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121534438946442871144738777 91150829209832153358554083)
                  ·
                    refine ⟨136726243814748230037831125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91150829209832153358554083 136726243814748230037831125)
                    ·
                      refine ⟨3204521339408161641511667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136726243814748230037831125 3204521339408161641511667)
                      ·
                        rfl

theorem cell23_6240783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_6240783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240783 prefixEnd_6240783 := by exact prefixLift 6240783
  have htrace : WordTrace (prefixWord ++ tailWord_6240783) baseStart_6240783 baseEnd_6240783 := by
    simpa [prefixWord, tailWord_6240783, baseEnd_6240783] using wordTrace_append hprefix tailTrace_6240783
  have hstable : (prefixWord ++ tailWord_6240783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240783).length < 2 ^ (prefixWord ++ tailWord_6240783).sum := by decide
  have hdescent : baseEnd_6240783 < baseStart_6240783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240787 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 3]
def baseStart_6240787 : Nat := 118140960795 + 6240787 * 2 ^ 59
def prefixEnd_6240787 : Nat := 4983230072969 + 3 ^ 40 * 6240787 * 2
def baseEnd_6240787 : Nat := 3204523393330779625861649

theorem tailTrace_6240787 : CollatzResearch.WordTrace tailWord_6240787 prefixEnd_6240787 3204523393330779625861649 := by
  unfold tailWord_6240787
  simp only [CollatzResearch.WordTrace]
  refine ⟨227620201641702015408728615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151746801094468010272485743 227620201641702015408728615)
  ·
    refine ⟨341430302462553023113092923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227620201641702015408728615 341430302462553023113092923)
    ·
      refine ⟨512145453693829534669639385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341430302462553023113092923 512145453693829534669639385)
      ·
        refine ⟨384109090270372151002229539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512145453693829534669639385 384109090270372151002229539)
        ·
          refine ⟨576163635405558226503344309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384109090270372151002229539 576163635405558226503344309)
          ·
            refine ⟨54015340819271083734688529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 576163635405558226503344309 54015340819271083734688529)
            ·
              refine ⟨40511505614453312801016397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54015340819271083734688529 40511505614453312801016397)
              ·
                refine ⟨15191814605419992300381149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40511505614453312801016397 15191814605419992300381149)
                ·
                  refine ⟨5696930477032497112642931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15191814605419992300381149 5696930477032497112642931)
                  ·
                    refine ⟨8545395715548745668964397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696930477032497112642931 8545395715548745668964397)
                    ·
                      refine ⟨3204523393330779625861649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545395715548745668964397 3204523393330779625861649)
                      ·
                        rfl

theorem cell23_6240787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_6240787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240787 prefixEnd_6240787 := by exact prefixLift 6240787
  have htrace : WordTrace (prefixWord ++ tailWord_6240787) baseStart_6240787 baseEnd_6240787 := by
    simpa [prefixWord, tailWord_6240787, baseEnd_6240787] using wordTrace_append hprefix tailTrace_6240787
  have hstable : (prefixWord ++ tailWord_6240787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240787).length < 2 ^ (prefixWord ++ tailWord_6240787).sum := by decide
  have hdescent : baseEnd_6240787 < baseStart_6240787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240821 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_6240821 : Nat := 118140960795 + 6240821 * 2 ^ 59
def prefixEnd_6240821 : Nat := 4983230072969 + 3 ^ 40 * 6240821 * 2
def baseEnd_6240821 : Nat := 3204540851673032492836493

theorem tailTrace_6240821 : CollatzResearch.WordTrace tailWord_6240821 prefixEnd_6240821 3204540851673032492836493 := by
  unfold tailWord_6240821
  simp only [CollatzResearch.WordTrace]
  refine ⟨227621441723578839215466317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151747627815719226143644211 227621441723578839215466317)
  ·
    refine ⟨85358040646342064705799869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227621441723578839215466317 85358040646342064705799869)
    ·
      refine ⟨32009265242378274264674951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85358040646342064705799869 32009265242378274264674951)
      ·
        refine ⟨48013897863567411397012427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32009265242378274264674951 48013897863567411397012427)
        ·
          refine ⟨72020846795351117095518641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48013897863567411397012427 72020846795351117095518641)
          ·
            refine ⟨54015635096513337821638981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72020846795351117095518641 54015635096513337821638981)
            ·
              refine ⟨10127931580596250841557309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54015635096513337821638981 10127931580596250841557309)
              ·
                refine ⟨3797974342723594065583991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10127931580596250841557309 3797974342723594065583991)
                ·
                  refine ⟨5696961514085391098375987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797974342723594065583991 5696961514085391098375987)
                  ·
                    refine ⟨8545442271128086647563981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696961514085391098375987 8545442271128086647563981)
                    ·
                      refine ⟨3204540851673032492836493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545442271128086647563981 3204540851673032492836493)
                      ·
                        rfl

theorem cell23_6240821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_6240821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240821 prefixEnd_6240821 := by exact prefixLift 6240821
  have htrace : WordTrace (prefixWord ++ tailWord_6240821) baseStart_6240821 baseEnd_6240821 := by
    simpa [prefixWord, tailWord_6240821, baseEnd_6240821] using wordTrace_append hprefix tailTrace_6240821
  have hstable : (prefixWord ++ tailWord_6240821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240821).length < 2 ^ (prefixWord ++ tailWord_6240821).sum := by decide
  have hdescent : baseEnd_6240821 < baseStart_6240821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240837 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_6240837 : Nat := 118140960795 + 6240837 * 2 ^ 59
def prefixEnd_6240837 : Nat := 4983230072969 + 3 ^ 40 * 6240837 * 2
def baseEnd_6240837 : Nat := 1068183022454501476745473

theorem tailTrace_6240837 : CollatzResearch.WordTrace tailWord_6240837 prefixEnd_6240837 1068183022454501476745473 := by
  unfold tailWord_6240837
  simp only [CollatzResearch.WordTrace]
  refine ⟨227622025291520873948048765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151748016861013915965365843 227622025291520873948048765)
  ·
    refine ⟨85358259484320327730518287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227622025291520873948048765 85358259484320327730518287)
    ·
      refine ⟨128037389226480491595777431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85358259484320327730518287 128037389226480491595777431)
      ·
        refine ⟨192056083839720737393666147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128037389226480491595777431 192056083839720737393666147)
        ·
          refine ⟨288084125759581106090499221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192056083839720737393666147 288084125759581106090499221)
          ·
            refine ⟨13503943394980364347992151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288084125759581106090499221 13503943394980364347992151)
            ·
              refine ⟨20255915092470546521988227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503943394980364347992151 20255915092470546521988227)
              ·
                refine ⟨30383872638705819782982341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20255915092470546521988227 30383872638705819782982341)
                ·
                  refine ⟨5696976119757341209309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30383872638705819782982341 5696976119757341209309189)
                  ·
                    refine ⟨1068183022454501476745473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696976119757341209309189 1068183022454501476745473)
                    ·
                      rfl

theorem cell23_6240837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_6240837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240837 prefixEnd_6240837 := by exact prefixLift 6240837
  have htrace : WordTrace (prefixWord ++ tailWord_6240837) baseStart_6240837 baseEnd_6240837 := by
    simpa [prefixWord, tailWord_6240837, baseEnd_6240837] using wordTrace_append hprefix tailTrace_6240837
  have hstable : (prefixWord ++ tailWord_6240837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240837).length < 2 ^ (prefixWord ++ tailWord_6240837).sum := by decide
  have hdescent : baseEnd_6240837 < baseStart_6240837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240838 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6240838 : Nat := 118140960795 + 6240838 * 2 ^ 59
def prefixEnd_6240838 : Nat := 4983230072969 + 3 ^ 40 * 6240838 * 2
def baseEnd_6240838 : Nat := 3204549580844158926323915

theorem tailTrace_6240838 : CollatzResearch.WordTrace tailWord_6240838 prefixEnd_6240838 3204549580844158926323915 := by
  unfold tailWord_6240838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113189430141164097463599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151748041176344834079223445 7113189430141164097463599)
  ·
    refine ⟨10669784145211746146195399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113189430141164097463599 10669784145211746146195399)
    ·
      refine ⟨16004676217817619219293099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10669784145211746146195399 16004676217817619219293099)
      ·
        refine ⟨24007014326726428828939649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16004676217817619219293099 24007014326726428828939649)
        ·
          refine ⟨18005260745044821621704737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24007014326726428828939649 18005260745044821621704737)
          ·
            refine ⟨13503945558783616216278553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18005260745044821621704737 13503945558783616216278553)
            ·
              refine ⟨10127959169087712162208915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13503945558783616216278553 10127959169087712162208915)
              ·
                refine ⟨15191938753631568243313373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10127959169087712162208915 15191938753631568243313373)
                ·
                  refine ⟨5696977032611838091242515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15191938753631568243313373 5696977032611838091242515)
                  ·
                    refine ⟨8545465548917757136863773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696977032611838091242515 8545465548917757136863773)
                    ·
                      refine ⟨3204549580844158926323915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545465548917757136863773 3204549580844158926323915)
                      ·
                        rfl

theorem cell23_6240838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6240838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240838 prefixEnd_6240838 := by exact prefixLift 6240838
  have htrace : WordTrace (prefixWord ++ tailWord_6240838) baseStart_6240838 baseEnd_6240838 := by
    simpa [prefixWord, tailWord_6240838, baseEnd_6240838] using wordTrace_append hprefix tailTrace_6240838
  have hstable : (prefixWord ++ tailWord_6240838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240838).length < 2 ^ (prefixWord ++ tailWord_6240838).sum := by decide
  have hdescent : baseEnd_6240838 < baseStart_6240838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240840 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6240840 : Nat := 118140960795 + 6240840 * 2 ^ 59
def prefixEnd_6240840 : Nat := 4983230072969 + 3 ^ 40 * 6240840 * 2
def baseEnd_6240840 : Nat := 3204550607805467918498905

theorem tailTrace_6240840 : CollatzResearch.WordTrace tailWord_6240840 prefixEnd_6240840 3204550607805467918498905 := by
  unfold tailWord_6240840
  simp only [CollatzResearch.WordTrace]
  refine ⟨113811067355255002730203987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151748089807006670306938649 113811067355255002730203987)
  ·
    refine ⟨170716601032882504095305981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113811067355255002730203987 170716601032882504095305981)
    ·
      refine ⟨64018725387330939035739743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170716601032882504095305981 64018725387330939035739743)
      ·
        refine ⟨96028088080996408553609615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64018725387330939035739743 96028088080996408553609615)
        ·
          refine ⟨144042132121494612830414423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96028088080996408553609615 144042132121494612830414423)
          ·
            refine ⟨216063198182241919245621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144042132121494612830414423 216063198182241919245621635)
            ·
              refine ⟨324094797273362878868432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216063198182241919245621635 324094797273362878868432453)
              ·
                refine ⟨60767774488755539787831085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324094797273362878868432453 60767774488755539787831085)
                ·
                  refine ⟨22787915433283327420436657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60767774488755539787831085 22787915433283327420436657)
                  ·
                    refine ⟨17090936574962495565327493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22787915433283327420436657 17090936574962495565327493)
                    ·
                      refine ⟨3204550607805467918498905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17090936574962495565327493 3204550607805467918498905)
                      ·
                        rfl

theorem cell23_6240840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6240840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240840 prefixEnd_6240840 := by exact prefixLift 6240840
  have htrace : WordTrace (prefixWord ++ tailWord_6240840) baseStart_6240840 baseEnd_6240840 := by
    simpa [prefixWord, tailWord_6240840, baseEnd_6240840] using wordTrace_append hprefix tailTrace_6240840
  have hstable : (prefixWord ++ tailWord_6240840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240840).length < 2 ^ (prefixWord ++ tailWord_6240840).sum := by decide
  have hdescent : baseEnd_6240840 < baseStart_6240840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240850 : List Nat := [3, 2, 2, 1, 2, 1, 2, 10]
def baseStart_6240850 : Nat := 118140960795 + 6240850 * 2 ^ 59
def prefixEnd_6240850 : Nat := 4983230072969 + 3 ^ 40 * 6240850 * 2
def baseEnd_6240850 : Nat := 118687249726370847384217

theorem tailTrace_6240850 : CollatzResearch.WordTrace tailWord_6240850 prefixEnd_6240850 118687249726370847384217 := by
  unfold tailWord_6240850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56905624860118444292068001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151748332960315851445514669 56905624860118444292068001)
  ·
    refine ⟨42679218645088833219051001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56905624860118444292068001 42679218645088833219051001)
    ·
      refine ⟨32009413983816624914288251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42679218645088833219051001 32009413983816624914288251)
      ·
        refine ⟨48014120975724937371432377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32009413983816624914288251 48014120975724937371432377)
        ·
          refine ⟨36010590731793703028574283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48014120975724937371432377 36010590731793703028574283)
          ·
            refine ⟨54015886097690554542861425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36010590731793703028574283 54015886097690554542861425)
            ·
              refine ⟨40511914573267915907146069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54015886097690554542861425 40511914573267915907146069)
              ·
                refine ⟨118687249726370847384217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40511914573267915907146069 118687249726370847384217)
                ·
                  rfl

theorem cell23_6240850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_6240850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240850 prefixEnd_6240850 := by exact prefixLift 6240850
  have htrace : WordTrace (prefixWord ++ tailWord_6240850) baseStart_6240850 baseEnd_6240850 := by
    simpa [prefixWord, tailWord_6240850, baseEnd_6240850] using wordTrace_append hprefix tailTrace_6240850
  have hstable : (prefixWord ++ tailWord_6240850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240850).length < 2 ^ (prefixWord ++ tailWord_6240850).sum := by decide
  have hdescent : baseEnd_6240850 < baseStart_6240850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240961 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6240961 : Nat := 118140960795 + 6240961 * 2 ^ 59
def prefixEnd_6240961 : Nat := 4983230072969 + 3 ^ 40 * 6240961 * 2
def baseEnd_6240961 : Nat := 1068204246321553981695283

theorem tailTrace_6240961 : CollatzResearch.WordTrace tailWord_6240961 prefixEnd_6240961 1068204246321553981695283 := by
  unfold tailWord_6240961
  simp only [CollatzResearch.WordTrace]
  refine ⟨227626547943071643125562737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151751031962047762083708491 227626547943071643125562737)
  ·
    refine ⟨170719910957303732344172053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227626547943071643125562737 170719910957303732344172053)
    ·
      refine ⟨8002495826123612453633065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170719910957303732344172053 8002495826123612453633065)
      ·
        refine ⟨6001871869592709340224799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8002495826123612453633065 6001871869592709340224799)
        ·
          refine ⟨9002807804389064010337199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001871869592709340224799 9002807804389064010337199)
          ·
            refine ⟨13504211706583596015505799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002807804389064010337199 13504211706583596015505799)
            ·
              refine ⟨20256317559875394023258699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13504211706583596015505799 20256317559875394023258699)
              ·
                refine ⟨30384476339813091034888049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20256317559875394023258699 30384476339813091034888049)
                ·
                  refine ⟨22788357254859818276166037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30384476339813091034888049 22788357254859818276166037)
                  ·
                    refine ⟨1068204246321553981695283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22788357254859818276166037 1068204246321553981695283)
                    ·
                      rfl

theorem cell23_6240961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6240961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240961 prefixEnd_6240961 := by exact prefixLift 6240961
  have htrace : WordTrace (prefixWord ++ tailWord_6240961) baseStart_6240961 baseEnd_6240961 := by
    simpa [prefixWord, tailWord_6240961, baseEnd_6240961] using wordTrace_append hprefix tailTrace_6240961
  have hstable : (prefixWord ++ tailWord_6240961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240961).length < 2 ^ (prefixWord ++ tailWord_6240961).sum := by decide
  have hdescent : baseEnd_6240961 < baseStart_6240961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240964 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6240964 : Nat := 118140960795 + 6240964 * 2 ^ 59
def prefixEnd_6240964 : Nat := 4983230072969 + 3 ^ 40 * 6240964 * 2
def baseEnd_6240964 : Nat := 3204614279406625433348335

theorem tailTrace_6240964 : CollatzResearch.WordTrace tailWord_6240964 prefixEnd_6240964 3204614279406625433348335 := by
  unfold tailWord_6240964
  simp only [CollatzResearch.WordTrace]
  refine ⟨113813328681030387318960973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151751104908040516425281297 113813328681030387318960973)
  ·
    refine ⟨42679998255386395244610365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113813328681030387318960973 42679998255386395244610365)
    ·
      refine ⟨16004999345769898216728887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42679998255386395244610365 16004999345769898216728887)
      ·
        refine ⟨24007499018654847325093331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16004999345769898216728887 24007499018654847325093331)
        ·
          refine ⟨36011248527982270987639997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24007499018654847325093331 36011248527982270987639997)
          ·
            refine ⟨13504218197993351620364999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36011248527982270987639997 13504218197993351620364999)
            ·
              refine ⟨20256327296990027430547499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13504218197993351620364999 20256327296990027430547499)
              ·
                refine ⟨30384490945485041145821249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20256327296990027430547499 30384490945485041145821249)
                ·
                  refine ⟨22788368209113780859365937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30384490945485041145821249 22788368209113780859365937)
                  ·
                    refine ⟨17091276156835335644524453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22788368209113780859365937 17091276156835335644524453)
                    ·
                      refine ⟨3204614279406625433348335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17091276156835335644524453 3204614279406625433348335)
                      ·
                        rfl

theorem cell23_6240964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6240964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240964 prefixEnd_6240964 := by exact prefixLift 6240964
  have htrace : WordTrace (prefixWord ++ tailWord_6240964) baseStart_6240964 baseEnd_6240964 := by
    simpa [prefixWord, tailWord_6240964, baseEnd_6240964] using wordTrace_append hprefix tailTrace_6240964
  have hstable : (prefixWord ++ tailWord_6240964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240964).length < 2 ^ (prefixWord ++ tailWord_6240964).sum := by decide
  have hdescent : baseEnd_6240964 < baseStart_6240964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241034 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_6241034 : Nat := 118140960795 + 6241034 * 2 ^ 59
def prefixEnd_6241034 : Nat := 4983230072969 + 3 ^ 40 * 6241034 * 2
def baseEnd_6241034 : Nat := 1068216741017480053157671

theorem tailTrace_6241034 : CollatzResearch.WordTrace tailWord_6241034 prefixEnd_6241034 1068216741017480053157671 := by
  unfold tailWord_6241034
  simp only [CollatzResearch.WordTrace]
  refine ⟨56907302617951794148242539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151752806981204784395313437 56907302617951794148242539)
  ·
    refine ⟨85360953926927691222363809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56907302617951794148242539 85360953926927691222363809)
    ·
      refine ⟨64020715445195768416772857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85360953926927691222363809 64020715445195768416772857)
      ·
        refine ⟨48015536583896826312579643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64020715445195768416772857 48015536583896826312579643)
        ·
          refine ⟨72023304875845239468869465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48015536583896826312579643 72023304875845239468869465)
          ·
            refine ⟨54017478656883929601652099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72023304875845239468869465 54017478656883929601652099)
            ·
              refine ⟨81026217985325894402478149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54017478656883929601652099 81026217985325894402478149)
              ·
                refine ⟨15192415872248605200464653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81026217985325894402478149 15192415872248605200464653)
                ·
                  refine ⟨5697155952093226950174245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15192415872248605200464653 5697155952093226950174245)
                  ·
                    refine ⟨1068216741017480053157671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697155952093226950174245 1068216741017480053157671)
                    ·
                      rfl

theorem cell23_6241034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_6241034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241034 prefixEnd_6241034 := by exact prefixLift 6241034
  have htrace : WordTrace (prefixWord ++ tailWord_6241034) baseStart_6241034 baseEnd_6241034 := by
    simpa [prefixWord, tailWord_6241034, baseEnd_6241034] using wordTrace_append hprefix tailTrace_6241034
  have hstable : (prefixWord ++ tailWord_6241034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241034).length < 2 ^ (prefixWord ++ tailWord_6241034).sum := by decide
  have hdescent : baseEnd_6241034 < baseStart_6241034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241064 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 6]
def baseStart_6241064 : Nat := 118140960795 + 6241064 * 2 ^ 59
def prefixEnd_6241064 : Nat := 4983230072969 + 3 ^ 40 * 6241064 * 2
def baseEnd_6241064 : Nat := 356073958608008338010875

theorem tailTrace_6241064 : CollatzResearch.WordTrace tailWord_6241064 prefixEnd_6241064 356073958608008338010875 := by
  unfold tailWord_6241064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113815152330849245858281123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151753536441132327811041497 113815152330849245858281123)
  ·
    refine ⟨170722728496273868787421685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113815152330849245858281123 170722728496273868787421685)
    ·
      refine ⟨16005255796525675198820783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170722728496273868787421685 16005255796525675198820783)
      ·
        refine ⟨24007883694788512798231175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16005255796525675198820783 24007883694788512798231175)
        ·
          refine ⟨36011825542182769197346763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24007883694788512798231175 36011825542182769197346763)
          ·
            refine ⟨54017738313274153796020145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36011825542182769197346763 54017738313274153796020145)
            ·
              refine ⟨40513303734955615347015109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54017738313274153796020145 40513303734955615347015109)
              ·
                refine ⟨7596244450304177877565333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40513303734955615347015109 7596244450304177877565333)
                ·
                  refine ⟨356073958608008338010875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7596244450304177877565333 356073958608008338010875)
                  ·
                    rfl

theorem cell23_6241064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_6241064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241064 prefixEnd_6241064 := by exact prefixLift 6241064
  have htrace : WordTrace (prefixWord ++ tailWord_6241064) baseStart_6241064 baseEnd_6241064 := by
    simpa [prefixWord, tailWord_6241064, baseEnd_6241064] using wordTrace_append hprefix tailTrace_6241064
  have hstable : (prefixWord ++ tailWord_6241064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241064).length < 2 ^ (prefixWord ++ tailWord_6241064).sum := by decide
  have hdescent : baseEnd_6241064 < baseStart_6241064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241068 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_6241068 : Nat := 118140960795 + 6241068 * 2 ^ 59
def prefixEnd_6241068 : Nat := 4983230072969 + 3 ^ 40 * 6241068 * 2
def baseEnd_6241068 : Nat := 1068222560464897675482619

theorem tailTrace_6241068 : CollatzResearch.WordTrace tailWord_6241068 prefixEnd_6241068 1068222560464897675482619 := by
  unfold tailWord_6241068
  simp only [CollatzResearch.WordTrace]
  refine ⟨113815225276842000199853929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151753633702456000266471905 113815225276842000199853929)
  ·
    refine ⟨85361418957631500149890447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113815225276842000199853929 85361418957631500149890447)
    ·
      refine ⟨128042128436447250224835671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85361418957631500149890447 128042128436447250224835671)
      ·
        refine ⟨192063192654670875337253507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128042128436447250224835671 192063192654670875337253507)
        ·
          refine ⟨288094788982006313005880261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192063192654670875337253507 288094788982006313005880261)
          ·
            refine ⟨54017772934126183688602549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288094788982006313005880261 54017772934126183688602549)
            ·
              refine ⟨5064166212574329720806489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54017772934126183688602549 5064166212574329720806489)
              ·
                refine ⟨3798124659430747290604867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064166212574329720806489 3798124659430747290604867)
                ·
                  refine ⟨5697186989146120935907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798124659430747290604867 5697186989146120935907301)
                  ·
                    refine ⟨1068222560464897675482619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697186989146120935907301 1068222560464897675482619)
                    ·
                      rfl

theorem cell23_6241068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_6241068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241068 prefixEnd_6241068 := by exact prefixLift 6241068
  have htrace : WordTrace (prefixWord ++ tailWord_6241068) baseStart_6241068 baseEnd_6241068 := by
    simpa [prefixWord, tailWord_6241068, baseEnd_6241068] using wordTrace_append hprefix tailTrace_6241068
  have hstable : (prefixWord ++ tailWord_6241068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241068).length < 2 ^ (prefixWord ++ tailWord_6241068).sum := by decide
  have hdescent : baseEnd_6241068 < baseStart_6241068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241125 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_6241125 : Nat := 118140960795 + 6241125 * 2 ^ 59
def prefixEnd_6241125 : Nat := 4983230072969 + 3 ^ 40 * 6241125 * 2
def baseEnd_6241125 : Nat := 3204696949791999303435095

theorem tailTrace_6241125 : CollatzResearch.WordTrace tailWord_6241125 prefixEnd_6241125 3204696949791999303435095 := by
  unfold tailWord_6241125
  simp only [CollatzResearch.WordTrace]
  refine ⟨227632529514477499134532829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151755019676318332756355219 227632529514477499134532829)
  ·
    refine ⟨85362198567929062175449811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227632529514477499134532829 85362198567929062175449811)
    ·
      refine ⟨128043297851893593263174717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85362198567929062175449811 128043297851893593263174717)
      ·
        refine ⟨48016236694460097473690519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128043297851893593263174717 48016236694460097473690519)
        ·
          refine ⟨72024355041690146210535779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48016236694460097473690519 72024355041690146210535779)
          ·
            refine ⟨108036532562535219315803669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72024355041690146210535779 108036532562535219315803669)
            ·
              refine ⟨5064212463868838405428297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108036532562535219315803669 5064212463868838405428297)
              ·
                refine ⟨3798159347901628804071223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064212463868838405428297 3798159347901628804071223)
                ·
                  refine ⟨5697239021852443206106835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798159347901628804071223 5697239021852443206106835)
                  ·
                    refine ⟨8545858532778664809160253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697239021852443206106835 8545858532778664809160253)
                    ·
                      refine ⟨3204696949791999303435095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8545858532778664809160253 3204696949791999303435095)
                      ·
                        rfl

theorem cell23_6241125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_6241125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241125 prefixEnd_6241125 := by exact prefixLift 6241125
  have htrace : WordTrace (prefixWord ++ tailWord_6241125) baseStart_6241125 baseEnd_6241125 := by
    simpa [prefixWord, tailWord_6241125, baseEnd_6241125] using wordTrace_append hprefix tailTrace_6241125
  have hstable : (prefixWord ++ tailWord_6241125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241125).length < 2 ^ (prefixWord ++ tailWord_6241125).sum := by decide
  have hdescent : baseEnd_6241125 < baseStart_6241125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241141 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6241141 : Nat := 118140960795 + 6241141 * 2 ^ 59
def prefixEnd_6241141 : Nat := 4983230072969 + 3 ^ 40 * 6241141 * 2
def baseEnd_6241141 : Nat := 1068235055160823746945007

theorem tailTrace_6241141 : CollatzResearch.WordTrace tailWord_6241141 prefixEnd_6241141 1068235055160823746945007 := by
  unfold tailWord_6241141
  simp only [CollatzResearch.WordTrace]
  refine ⟨227633113082419533867115277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151755408721613022578076851 227633113082419533867115277)
  ·
    refine ⟨85362417405907325200168229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227633113082419533867115277 85362417405907325200168229)
    ·
      refine ⟨16005453263607623475031543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85362417405907325200168229 16005453263607623475031543)
      ·
        refine ⟨24008179895411435212547315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16005453263607623475031543 24008179895411435212547315)
        ·
          refine ⟨36012269843117152818820973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24008179895411435212547315 36012269843117152818820973)
          ·
            refine ⟨13504601191168932307057865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36012269843117152818820973 13504601191168932307057865)
            ·
              refine ⟨10128450893376699230293399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13504601191168932307057865 10128450893376699230293399)
              ·
                refine ⟨15192676340065048845440099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128450893376699230293399 15192676340065048845440099)
                ·
                  refine ⟨22789014510097573268160149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15192676340065048845440099 22789014510097573268160149)
                  ·
                    refine ⟨1068235055160823746945007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22789014510097573268160149 1068235055160823746945007)
                    ·
                      rfl

theorem cell23_6241141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6241141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241141 prefixEnd_6241141 := by exact prefixLift 6241141
  have htrace : WordTrace (prefixWord ++ tailWord_6241141) baseStart_6241141 baseEnd_6241141 := by
    simpa [prefixWord, tailWord_6241141, baseEnd_6241141] using wordTrace_append hprefix tailTrace_6241141
  have hstable : (prefixWord ++ tailWord_6241141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241141).length < 2 ^ (prefixWord ++ tailWord_6241141).sum := by decide
  have hdescent : baseEnd_6241141 < baseStart_6241141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241208 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_6241208 : Nat := 118140960795 + 6241208 * 2 ^ 59
def prefixEnd_6241208 : Nat := 4983230072969 + 3 ^ 40 * 6241208 * 2
def baseEnd_6241208 : Nat := 3204739568686322478697213

theorem tailTrace_6241208 : CollatzResearch.WordTrace tailWord_6241208 prefixEnd_6241208 3204739568686322478697213 := by
  unfold tailWord_6241208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113817778386588402154902139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151757037848784536206536185 113817778386588402154902139)
  ·
    refine ⟨170726667579882603232353209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113817778386588402154902139 170726667579882603232353209)
    ·
      refine ⟨128045000684911952424264907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170726667579882603232353209 128045000684911952424264907)
      ·
        refine ⟨192067501027367928636397361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128045000684911952424264907 192067501027367928636397361)
        ·
          refine ⟨144050625770525946477298021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192067501027367928636397361 144050625770525946477298021)
          ·
            refine ⟨27009492331973614964493379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144050625770525946477298021 27009492331973614964493379)
            ·
              refine ⟨40514238497960422446740069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27009492331973614964493379 40514238497960422446740069)
              ·
                refine ⟨7596419718367579208763763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40514238497960422446740069 7596419718367579208763763)
                ·
                  refine ⟨11394629577551368813145645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596419718367579208763763 11394629577551368813145645)
                  ·
                    refine ⟨4272986091581763304929617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11394629577551368813145645 4272986091581763304929617)
                    ·
                      refine ⟨3204739568686322478697213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272986091581763304929617 3204739568686322478697213)
                      ·
                        rfl

theorem cell23_6241208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_6241208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241208 prefixEnd_6241208 := by exact prefixLift 6241208
  have htrace : WordTrace (prefixWord ++ tailWord_6241208) baseStart_6241208 baseEnd_6241208 := by
    simpa [prefixWord, tailWord_6241208, baseEnd_6241208] using wordTrace_append hprefix tailTrace_6241208
  have hstable : (prefixWord ++ tailWord_6241208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241208).length < 2 ^ (prefixWord ++ tailWord_6241208).sum := by decide
  have hdescent : baseEnd_6241208 < baseStart_6241208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241222 : List Nat := [6, 1, 3, 1, 1, 2, 9]
def baseStart_6241222 : Nat := 118140960795 + 6241222 * 2 ^ 59
def prefixEnd_6241222 : Nat := 4983230072969 + 3 ^ 40 * 6241222 * 2
def baseEnd_6241222 : Nat := 39564774782907227455829

theorem tailTrace_6241222 : CollatzResearch.WordTrace tailWord_6241222 prefixEnd_6241222 39564774782907227455829 := by
  unfold tailWord_6241222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113627106097690146900435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151757378263417389800542613 7113627106097690146900435)
  ·
    refine ⟨10670440659146535220350653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113627106097690146900435 10670440659146535220350653)
    ·
      refine ⟨4001415247179950707631495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10670440659146535220350653 4001415247179950707631495)
      ·
        refine ⟨6002122870769926061447243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001415247179950707631495 6002122870769926061447243)
        ·
          refine ⟨9003184306154889092170865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002122870769926061447243 9003184306154889092170865)
          ·
            refine ⟨6752388229616166819128149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003184306154889092170865 6752388229616166819128149)
            ·
              refine ⟨39564774782907227455829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6752388229616166819128149 39564774782907227455829)
              ·
                rfl

theorem cell23_6241222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 9].length) (baseStart_6241222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241222 prefixEnd_6241222 := by exact prefixLift 6241222
  have htrace : WordTrace (prefixWord ++ tailWord_6241222) baseStart_6241222 baseEnd_6241222 := by
    simpa [prefixWord, tailWord_6241222, baseEnd_6241222] using wordTrace_append hprefix tailTrace_6241222
  have hstable : (prefixWord ++ tailWord_6241222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241222).length < 2 ^ (prefixWord ++ tailWord_6241222).sum := by decide
  have hdescent : baseEnd_6241222 < baseStart_6241222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241274 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_6241274 : Nat := 118140960795 + 6241274 * 2 ^ 59
def prefixEnd_6241274 : Nat := 4983230072969 + 3 ^ 40 * 6241274 * 2
def baseEnd_6241274 : Nat := 1068257819469839740157303

theorem tailTrace_6241274 : CollatzResearch.WordTrace tailWord_6241274 prefixEnd_6241274 1068257819469839740157303 := by
  unfold tailWord_6241274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56909490997734424395426719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151758642660625131721137917 56909490997734424395426719)
  ·
    refine ⟨85364236496601636593140079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56909490997734424395426719 85364236496601636593140079)
    ·
      refine ⟨128046354744902454889710119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85364236496601636593140079 128046354744902454889710119)
      ·
        refine ⟨192069532117353682334565179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128046354744902454889710119 192069532117353682334565179)
        ·
          refine ⟨288104298176030523501847769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192069532117353682334565179 288104298176030523501847769)
          ·
            refine ⟨216078223632022892626385827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288104298176030523501847769 216078223632022892626385827)
            ·
              refine ⟨324117335448034338939578741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216078223632022892626385827 324117335448034338939578741)
              ·
                refine ⟨30386000198253219275585507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324117335448034338939578741 30386000198253219275585507)
                ·
                  refine ⟨45579000297379828913378261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30386000198253219275585507 45579000297379828913378261)
                  ·
                    refine ⟨1068257819469839740157303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45579000297379828913378261 1068257819469839740157303)
                    ·
                      rfl

theorem cell23_6241274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_6241274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241274 prefixEnd_6241274 := by exact prefixLift 6241274
  have htrace : WordTrace (prefixWord ++ tailWord_6241274) baseStart_6241274 baseEnd_6241274 := by
    simpa [prefixWord, tailWord_6241274, baseEnd_6241274] using wordTrace_append hprefix tailTrace_6241274
  have hstable : (prefixWord ++ tailWord_6241274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241274).length < 2 ^ (prefixWord ++ tailWord_6241274).sum := by decide
  have hdescent : baseEnd_6241274 < baseStart_6241274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241291 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 2, 5]
def baseStart_6241291 : Nat := 118140960795 + 6241291 * 2 ^ 59
def prefixEnd_6241291 : Nat := 4983230072969 + 3 ^ 40 * 6241291 * 2
def baseEnd_6241291 : Nat := 1068260729193548551319777

theorem tailTrace_6241291 : CollatzResearch.WordTrace tailWord_6241291 prefixEnd_6241291 1068260729193548551319777 := by
  unfold tailWord_6241291
  simp only [CollatzResearch.WordTrace]
  refine ⟨227638584031876109485075727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151759056021250739656717151 227638584031876109485075727)
  ·
    refine ⟨341457876047814164227613591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227638584031876109485075727 341457876047814164227613591)
    ·
      refine ⟨512186814071721246341420387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341457876047814164227613591 512186814071721246341420387)
      ·
        refine ⟨768280221107581869512130581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512186814071721246341420387 768280221107581869512130581)
        ·
          refine ⟨36013135364417900133381121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 768280221107581869512130581 36013135364417900133381121)
          ·
            refine ⟨27009851523313425100035841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36013135364417900133381121 27009851523313425100035841)
            ·
              refine ⟨20257388642485068825026881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27009851523313425100035841 20257388642485068825026881)
              ·
                refine ⟨15193041481863801618770161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20257388642485068825026881 15193041481863801618770161)
                ·
                  refine ⟨11394781111397851214077621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15193041481863801618770161 11394781111397851214077621)
                  ·
                    refine ⟨1068260729193548551319777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11394781111397851214077621 1068260729193548551319777)
                    ·
                      rfl

theorem cell23_6241291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].length) (baseStart_6241291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241291 prefixEnd_6241291 := by exact prefixLift 6241291
  have htrace : WordTrace (prefixWord ++ tailWord_6241291) baseStart_6241291 baseEnd_6241291 := by
    simpa [prefixWord, tailWord_6241291, baseEnd_6241291] using wordTrace_append hprefix tailTrace_6241291
  have hstable : (prefixWord ++ tailWord_6241291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241291).length < 2 ^ (prefixWord ++ tailWord_6241291).sum := by decide
  have hdescent : baseEnd_6241291 < baseStart_6241291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241301 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6241301 : Nat := 118140960795 + 6241301 * 2 ^ 59
def prefixEnd_6241301 : Nat := 4983230072969 + 3 ^ 40 * 6241301 * 2
def baseEnd_6241301 : Nat := 3204787322387190614834285

theorem tailTrace_6241301 : CollatzResearch.WordTrace tailWord_6241301 prefixEnd_6241301 3204787322387190614834285 := by
  unfold tailWord_6241301
  simp only [CollatzResearch.WordTrace]
  refine ⟨227638948761839881192939757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151759299174559920795293171 227638948761839881192939757)
  ·
    refine ⟨85364605785689955447352409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227638948761839881192939757 85364605785689955447352409)
    ·
      refine ⟨64023454339267466585514307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85364605785689955447352409 64023454339267466585514307)
      ·
        refine ⟨96035181508901199878271461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64023454339267466585514307 96035181508901199878271461)
        ·
          refine ⟨18006596532918974977175899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96035181508901199878271461 18006596532918974977175899)
          ·
            refine ⟨27009894799378462465763849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006596532918974977175899 27009894799378462465763849)
            ·
              refine ⟨20257421099533846849322887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27009894799378462465763849 20257421099533846849322887)
              ·
                refine ⟨30386131649300770273984331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20257421099533846849322887 30386131649300770273984331)
                ·
                  refine ⟨45579197473951155410976497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30386131649300770273984331 45579197473951155410976497)
                  ·
                    refine ⟨34184398105463366558232373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45579197473951155410976497 34184398105463366558232373)
                    ·
                      refine ⟨3204787322387190614834285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34184398105463366558232373 3204787322387190614834285)
                      ·
                        rfl

theorem cell23_6241301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6241301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241301 prefixEnd_6241301 := by exact prefixLift 6241301
  have htrace : WordTrace (prefixWord ++ tailWord_6241301) baseStart_6241301 baseEnd_6241301 := by
    simpa [prefixWord, tailWord_6241301, baseEnd_6241301] using wordTrace_append hprefix tailTrace_6241301
  have hstable : (prefixWord ++ tailWord_6241301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241301).length < 2 ^ (prefixWord ++ tailWord_6241301).sum := by decide
  have hdescent : baseEnd_6241301 < baseStart_6241301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241341 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6241341 : Nat := 118140960795 + 6241341 * 2 ^ 59
def prefixEnd_6241341 : Nat := 4983230072969 + 3 ^ 40 * 6241341 * 2
def baseEnd_6241341 : Nat := 3204807861613370458334101

theorem tailTrace_6241341 : CollatzResearch.WordTrace tailWord_6241341 prefixEnd_6241341 3204807861613370458334101 := by
  unfold tailWord_6241341
  simp only [CollatzResearch.WordTrace]
  refine ⟨227640407681694968024395877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151760271787796645349597251 227640407681694968024395877)
  ·
    refine ⟨42682576440317806504574227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227640407681694968024395877 42682576440317806504574227)
    ·
      refine ⟨64023864660476709756861341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42682576440317806504574227 64023864660476709756861341)
      ·
        refine ⟨24008949247678766158823003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64023864660476709756861341 24008949247678766158823003)
        ·
          refine ⟨36013423871518149238234505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24008949247678766158823003 36013423871518149238234505)
          ·
            refine ⟨27010067903638611928675879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36013423871518149238234505 27010067903638611928675879)
            ·
              refine ⟨40515101855457917893013819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27010067903638611928675879 40515101855457917893013819)
              ·
                refine ⟨60772652783186876839520729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40515101855457917893013819 60772652783186876839520729)
                ·
                  refine ⟨45579489587390157629640547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60772652783186876839520729 45579489587390157629640547)
                  ·
                    refine ⟨68369234381085236444460821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45579489587390157629640547 68369234381085236444460821)
                    ·
                      refine ⟨3204807861613370458334101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68369234381085236444460821 3204807861613370458334101)
                      ·
                        rfl

theorem cell23_6241341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6241341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241341 prefixEnd_6241341 := by exact prefixLift 6241341
  have htrace : WordTrace (prefixWord ++ tailWord_6241341) baseStart_6241341 baseEnd_6241341 := by
    simpa [prefixWord, tailWord_6241341, baseEnd_6241341] using wordTrace_append hprefix tailTrace_6241341
  have hstable : (prefixWord ++ tailWord_6241341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241341).length < 2 ^ (prefixWord ++ tailWord_6241341).sum := by decide
  have hdescent : baseEnd_6241341 < baseStart_6241341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241351 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 8]
def baseStart_6241351 : Nat := 118140960795 + 6241351 * 2 ^ 59
def prefixEnd_6241351 : Nat := 4983230072969 + 3 ^ 40 * 6241351 * 2
def baseEnd_6241351 : Nat := 356090332935546157689895

theorem tailTrace_6241351 : CollatzResearch.WordTrace tailWord_6241351 prefixEnd_6241351 356090332935546157689895 := by
  unfold tailWord_6241351
  simp only [CollatzResearch.WordTrace]
  refine ⟨227640772411658739732259907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151760514941105826488173271 227640772411658739732259907)
  ·
    refine ⟨341461158617488109598389861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227640772411658739732259907 341461158617488109598389861)
    ·
      refine ⟨64023967240779020549698099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341461158617488109598389861 64023967240779020549698099)
      ·
        refine ⟨96035950861168530824547149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64023967240779020549698099 96035950861168530824547149)
        ·
          refine ⟨36013481572938199059205181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96035950861168530824547149 36013481572938199059205181)
          ·
            refine ⟨13505055589851824647201943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36013481572938199059205181 13505055589851824647201943)
            ·
              refine ⟨20257583384777736970802915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13505055589851824647201943 20257583384777736970802915)
              ·
                refine ⟨30386375077166605456204373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20257583384777736970802915 30386375077166605456204373)
                ·
                  refine ⟨356090332935546157689895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30386375077166605456204373 356090332935546157689895)
                  ·
                    rfl

theorem cell23_6241351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 8].length) (baseStart_6241351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241351 prefixEnd_6241351 := by exact prefixLift 6241351
  have htrace : WordTrace (prefixWord ++ tailWord_6241351) baseStart_6241351 baseEnd_6241351 := by
    simpa [prefixWord, tailWord_6241351, baseEnd_6241351] using wordTrace_append hprefix tailTrace_6241351
  have hstable : (prefixWord ++ tailWord_6241351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241351).length < 2 ^ (prefixWord ++ tailWord_6241351).sum := by decide
  have hdescent : baseEnd_6241351 < baseStart_6241351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241368 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 6]
def baseStart_6241368 : Nat := 118140960795 + 6241368 * 2 ^ 59
def prefixEnd_6241368 : Nat := 4983230072969 + 3 ^ 40 * 6241368 * 2
def baseEnd_6241368 : Nat := 356091302843449094744053

theorem tailTrace_6241368 : CollatzResearch.WordTrace tailWord_6241368 prefixEnd_6241368 356091302843449094744053 := by
  unfold tailWord_6241368
  simp only [CollatzResearch.WordTrace]
  refine ⟨113820696226298575817814379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151760928301731434423752505 113820696226298575817814379)
  ·
    refine ⟨170731044339447863726721569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113820696226298575817814379 170731044339447863726721569)
    ·
      refine ⟨128048283254585897795041177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170731044339447863726721569 128048283254585897795041177)
      ·
        refine ⟨96036212440939423346280883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128048283254585897795041177 96036212440939423346280883)
        ·
          refine ⟨144054318661409135019421325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96036212440939423346280883 144054318661409135019421325)
          ·
            refine ⟨54020369498028425632282997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144054318661409135019421325 54020369498028425632282997)
            ·
              refine ⟨5064409640440164903026531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54020369498028425632282997 5064409640440164903026531)
              ·
                refine ⟨7596614460660247354539797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064409640440164903026531 7596614460660247354539797)
                ·
                  refine ⟨356091302843449094744053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7596614460660247354539797 356091302843449094744053)
                  ·
                    rfl

theorem cell23_6241368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_6241368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241368 prefixEnd_6241368 := by exact prefixLift 6241368
  have htrace : WordTrace (prefixWord ++ tailWord_6241368) baseStart_6241368 baseEnd_6241368 := by
    simpa [prefixWord, tailWord_6241368, baseEnd_6241368] using wordTrace_append hprefix tailTrace_6241368
  have hstable : (prefixWord ++ tailWord_6241368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241368).length < 2 ^ (prefixWord ++ tailWord_6241368).sum := by decide
  have hdescent : baseEnd_6241368 < baseStart_6241368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241388 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_6241388 : Nat := 118140960795 + 6241388 * 2 ^ 59
def prefixEnd_6241388 : Nat := 4983230072969 + 3 ^ 40 * 6241388 * 2
def baseEnd_6241388 : Nat := 3204831995204131774446385

theorem tailTrace_6241388 : CollatzResearch.WordTrace tailWord_6241388 prefixEnd_6241388 3204831995204131774446385 := by
  unfold tailWord_6241388
  simp only [CollatzResearch.WordTrace]
  refine ⟨113821060956262347525678409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151761414608349796700904545 113821060956262347525678409)
  ·
    refine ⟨85365795717196760644258807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113821060956262347525678409 85365795717196760644258807)
    ·
      refine ⟨128048693575795140966388211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85365795717196760644258807 128048693575795140966388211)
      ·
        refine ⟨192073040363692711449582317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128048693575795140966388211 192073040363692711449582317)
        ·
          refine ⟨72027390136384766793593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192073040363692711449582317 72027390136384766793593369)
          ·
            refine ⟨54020542602288575095195027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72027390136384766793593369 54020542602288575095195027)
            ·
              refine ⟨81030813903432862642792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54020542602288575095195027 81030813903432862642792541)
              ·
                refine ⟨30386555213787323491047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81030813903432862642792541 30386555213787323491047203)
                ·
                  refine ⟨45579832820680985236570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30386555213787323491047203 45579832820680985236570805)
                  ·
                    refine ⟨4273109326938842365928513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45579832820680985236570805 4273109326938842365928513)
                    ·
                      refine ⟨3204831995204131774446385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273109326938842365928513 3204831995204131774446385)
                      ·
                        rfl

theorem cell23_6241388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_6241388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241388 prefixEnd_6241388 := by exact prefixLift 6241388
  have htrace : WordTrace (prefixWord ++ tailWord_6241388) baseStart_6241388 baseEnd_6241388 := by
    simpa [prefixWord, tailWord_6241388, baseEnd_6241388] using wordTrace_append hprefix tailTrace_6241388
  have hstable : (prefixWord ++ tailWord_6241388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241388).length < 2 ^ (prefixWord ++ tailWord_6241388).sum := by decide
  have hdescent : baseEnd_6241388 < baseStart_6241388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241405 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_6241405 : Nat := 118140960795 + 6241405 * 2 ^ 59
def prefixEnd_6241405 : Nat := 4983230072969 + 3 ^ 40 * 6241405 * 2
def baseEnd_6241405 : Nat := 3204840724375258207933807

theorem tailTrace_6241405 : CollatzResearch.WordTrace tailWord_6241405 prefixEnd_6241405 3204840724375258207933807 := by
  unfold tailWord_6241405
  simp only [CollatzResearch.WordTrace]
  refine ⟨227642741953463106954725669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151761827968975404636483779 227642741953463106954725669)
  ·
    refine ⟨42683014116274332554011063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227642741953463106954725669 42683014116274332554011063)
    ·
      refine ⟨64024521174411498831016595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42683014116274332554011063 64024521174411498831016595)
      ·
        refine ⟨96036781761617248246524893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64024521174411498831016595 96036781761617248246524893)
        ·
          refine ⟨36013793160606468092446835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96036781761617248246524893 36013793160606468092446835)
          ·
            refine ⟨54020689740909702138670253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36013793160606468092446835 54020689740909702138670253)
            ·
              refine ⟨20257758652841138302001345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54020689740909702138670253 20257758652841138302001345)
              ·
                refine ⟨15193318989630853726501009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20257758652841138302001345 15193318989630853726501009)
                ·
                  refine ⟨11394989242223140294875757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15193318989630853726501009 11394989242223140294875757)
                  ·
                    refine ⟨4273120965833677610578409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11394989242223140294875757 4273120965833677610578409)
                    ·
                      refine ⟨3204840724375258207933807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273120965833677610578409 3204840724375258207933807)
                      ·
                        rfl

theorem cell23_6241405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_6241405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241405 prefixEnd_6241405 := by exact prefixLift 6241405
  have htrace : WordTrace (prefixWord ++ tailWord_6241405) baseStart_6241405 baseEnd_6241405 := by
    simpa [prefixWord, tailWord_6241405, baseEnd_6241405] using wordTrace_append hprefix tailTrace_6241405
  have hstable : (prefixWord ++ tailWord_6241405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241405).length < 2 ^ (prefixWord ++ tailWord_6241405).sum := by decide
  have hdescent : baseEnd_6241405 < baseStart_6241405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241406 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6241406 : Nat := 118140960795 + 6241406 * 2 ^ 59
def prefixEnd_6241406 : Nat := 4983230072969 + 3 ^ 40 * 6241406 * 2
def baseEnd_6241406 : Nat := 1068280412618637568007101

theorem tailTrace_6241406 : CollatzResearch.WordTrace tailWord_6241406 prefixEnd_6241406 1068280412618637568007101 := by
  unfold tailWord_6241406
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455347303307435515689009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151761852284306322750341381 28455347303307435515689009)
  ·
    refine ⟨21341510477480576636766757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28455347303307435515689009 21341510477480576636766757)
    ·
      refine ⟨4001533214527608119393767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21341510477480576636766757 4001533214527608119393767)
      ·
        refine ⟨6002299821791412179090651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001533214527608119393767 6002299821791412179090651)
        ·
          refine ⟨9003449732687118268635977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002299821791412179090651 9003449732687118268635977)
          ·
            refine ⟨6752587299515338701476983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003449732687118268635977 6752587299515338701476983)
            ·
              refine ⟨10128880949273008052215475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752587299515338701476983 10128880949273008052215475)
              ·
                refine ⟨15193321423909512078323213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128880949273008052215475 15193321423909512078323213)
                ·
                  refine ⟨5697495533966067029371205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15193321423909512078323213 5697495533966067029371205)
                  ·
                    refine ⟨1068280412618637568007101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697495533966067029371205 1068280412618637568007101)
                    ·
                      rfl

theorem cell23_6241406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6241406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241406 prefixEnd_6241406 := by exact prefixLift 6241406
  have htrace : WordTrace (prefixWord ++ tailWord_6241406) baseStart_6241406 baseEnd_6241406 := by
    simpa [prefixWord, tailWord_6241406, baseEnd_6241406] using wordTrace_append hprefix tailTrace_6241406
  have hstable : (prefixWord ++ tailWord_6241406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241406).length < 2 ^ (prefixWord ++ tailWord_6241406).sum := by decide
  have hdescent : baseEnd_6241406 < baseStart_6241406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241412 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_6241412 : Nat := 118140960795 + 6241412 * 2 ^ 59
def prefixEnd_6241412 : Nat := 4983230072969 + 3 ^ 40 * 6241412 * 2
def baseEnd_6241412 : Nat := 3204844318739839680546275

theorem tailTrace_6241412 : CollatzResearch.WordTrace tailWord_6241412 prefixEnd_6241412 3204844318739839680546275 := by
  unfold tailWord_6241412
  simp only [CollatzResearch.WordTrace]
  refine ⟨113821498632218873575115245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151761998176291831433486993 113821498632218873575115245)
  ·
    refine ⟨42683061987082077590668217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113821498632218873575115245 42683061987082077590668217)
    ·
      refine ⟨32012296490311558193001163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42683061987082077590668217 32012296490311558193001163)
      ·
        refine ⟨48018444735467337289501745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32012296490311558193001163 48018444735467337289501745)
        ·
          refine ⟨36013833551600502967126309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48018444735467337289501745 36013833551600502967126309)
          ·
            refine ⟨6752593790925094306336183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36013833551600502967126309 6752593790925094306336183)
            ·
              refine ⟨10128890686387641459504275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752593790925094306336183 10128890686387641459504275)
              ·
                refine ⟨15193336029581462189256413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128890686387641459504275 15193336029581462189256413)
                ·
                  refine ⟨5697501011093048320971155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15193336029581462189256413 5697501011093048320971155)
                  ·
                    refine ⟨8546251516639572481456733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697501011093048320971155 8546251516639572481456733)
                    ·
                      refine ⟨3204844318739839680546275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546251516639572481456733 3204844318739839680546275)
                      ·
                        rfl

theorem cell23_6241412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_6241412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241412 prefixEnd_6241412 := by exact prefixLift 6241412
  have htrace : WordTrace (prefixWord ++ tailWord_6241412) baseStart_6241412 baseEnd_6241412 := by
    simpa [prefixWord, tailWord_6241412, baseEnd_6241412] using wordTrace_append hprefix tailTrace_6241412
  have hstable : (prefixWord ++ tailWord_6241412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241412).length < 2 ^ (prefixWord ++ tailWord_6241412).sum := by decide
  have hdescent : baseEnd_6241412 < baseStart_6241412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241418 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6241418 : Nat := 118140960795 + 6241418 * 2 ^ 59
def prefixEnd_6241418 : Nat := 4983230072969 + 3 ^ 40 * 6241418 * 2
def baseEnd_6241418 : Nat := 3204847399623766657071247

theorem tailTrace_6241418 : CollatzResearch.WordTrace tailWord_6241418 prefixEnd_6241418 3204847399623766657071247 := by
  unfold tailWord_6241418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56910804025604002543737227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151762144068277340116632605 56910804025604002543737227)
  ·
    refine ⟨85366206038406003815605841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56910804025604002543737227 85366206038406003815605841)
    ·
      refine ⟨64024654528804502861704381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85366206038406003815605841 64024654528804502861704381)
      ·
        refine ⟨24009245448301688573139143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64024654528804502861704381 24009245448301688573139143)
        ·
          refine ⟨36013868172452532859708715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24009245448301688573139143 36013868172452532859708715)
          ·
            refine ⟨54020802258678799289563073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36013868172452532859708715 54020802258678799289563073)
            ·
              refine ⟨40515601694009099467172305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54020802258678799289563073 40515601694009099467172305)
              ·
                refine ⟨30386701270506824600379229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40515601694009099467172305 30386701270506824600379229)
                ·
                  refine ⟨11395012976440059225142211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30386701270506824600379229 11395012976440059225142211)
                  ·
                    refine ⟨17092519464660088837713317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11395012976440059225142211 17092519464660088837713317)
                    ·
                      refine ⟨3204847399623766657071247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17092519464660088837713317 3204847399623766657071247)
                      ·
                        rfl

theorem cell23_6241418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6241418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241418 prefixEnd_6241418 := by exact prefixLift 6241418
  have htrace : WordTrace (prefixWord ++ tailWord_6241418) baseStart_6241418 baseEnd_6241418 := by
    simpa [prefixWord, tailWord_6241418, baseEnd_6241418] using wordTrace_append hprefix tailTrace_6241418
  have hstable : (prefixWord ++ tailWord_6241418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241418).length < 2 ^ (prefixWord ++ tailWord_6241418).sum := by decide
  have hdescent : baseEnd_6241418 < baseStart_6241418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241441 : List Nat := [1, 2, 3, 3, 1, 1, 1, 11]
def baseStart_6241441 : Nat := 118140960795 + 6241441 * 2 ^ 59
def prefixEnd_6241441 : Nat := 4983230072969 + 3 ^ 40 * 6241441 * 2
def baseEnd_6241441 : Nat := 118698489247363706188283

theorem tailTrace_6241441 : CollatzResearch.WordTrace tailWord_6241441 prefixEnd_6241441 118698489247363706188283 := by
  unfold tailWord_6241441
  simp only [CollatzResearch.WordTrace]
  refine ⟨227644054981332685103036177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151762703320888456735357451 227644054981332685103036177)
  ·
    refine ⟨170733041235999513827277133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227644054981332685103036177 170733041235999513827277133)
    ·
      refine ⟨64024890463499817685228925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170733041235999513827277133 64024890463499817685228925)
      ·
        refine ⟨24009333923812431631960847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64024890463499817685228925 24009333923812431631960847)
        ·
          refine ⟨36014000885718647447941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24009333923812431631960847 36014000885718647447941271)
          ·
            refine ⟨54021001328577971171911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36014000885718647447941271 54021001328577971171911907)
            ·
              refine ⟨81031501992866956757867861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54021001328577971171911907 81031501992866956757867861)
              ·
                refine ⟨118698489247363706188283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81031501992866956757867861 118698489247363706188283)
                ·
                  rfl

theorem cell23_6241441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 11].length) (baseStart_6241441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241441 prefixEnd_6241441 := by exact prefixLift 6241441
  have htrace : WordTrace (prefixWord ++ tailWord_6241441) baseStart_6241441 baseEnd_6241441 := by
    simpa [prefixWord, tailWord_6241441, baseEnd_6241441] using wordTrace_append hprefix tailTrace_6241441
  have hstable : (prefixWord ++ tailWord_6241441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241441).length < 2 ^ (prefixWord ++ tailWord_6241441).sum := by decide
  have hdescent : baseEnd_6241441 < baseStart_6241441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241471 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 7]
def baseStart_6241471 : Nat := 118140960795 + 6241471 * 2 ^ 59
def prefixEnd_6241471 : Nat := 4983230072969 + 3 ^ 40 * 6241471 * 2
def baseEnd_6241471 : Nat := 1068291538032818316569501

theorem tailTrace_6241471 : CollatzResearch.WordTrace tailWord_6241471 prefixEnd_6241471 1068291538032818316569501 := by
  unfold tailWord_6241471
  simp only [CollatzResearch.WordTrace]
  refine ⟨227645149171224000226628267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151763432780816000151085511 227645149171224000226628267)
  ·
    refine ⟨341467723756836000339942401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227645149171224000226628267 341467723756836000339942401)
    ·
      refine ⟨256100792817627000254956801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341467723756836000339942401 256100792817627000254956801)
      ·
        refine ⟨192075594613220250191217601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256100792817627000254956801 192075594613220250191217601)
        ·
          refine ⟨144056695959915187643413201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192075594613220250191217601 144056695959915187643413201)
          ·
            refine ⟨108042521969936390732559901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144056695959915187643413201 108042521969936390732559901)
            ·
              refine ⟨40515945738726146524709963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108042521969936390732559901 40515945738726146524709963)
              ·
                refine ⟨60773918608089219787064945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40515945738726146524709963 60773918608089219787064945)
                ·
                  refine ⟨45580438956066914840298709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60773918608089219787064945 45580438956066914840298709)
                  ·
                    refine ⟨1068291538032818316569501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45580438956066914840298709 1068291538032818316569501)
                    ·
                      rfl

theorem cell23_6241471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_6241471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241471 prefixEnd_6241471 := by exact prefixLift 6241471
  have htrace : WordTrace (prefixWord ++ tailWord_6241471) baseStart_6241471 baseEnd_6241471 := by
    simpa [prefixWord, tailWord_6241471, baseEnd_6241471] using wordTrace_append hprefix tailTrace_6241471
  have hstable : (prefixWord ++ tailWord_6241471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241471).length < 2 ^ (prefixWord ++ tailWord_6241471).sum := by decide
  have hdescent : baseEnd_6241471 < baseStart_6241471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241492 : List Nat := [2, 4, 1, 4, 1, 1, 3, 7]
def baseStart_6241492 : Nat := 118140960795 + 6241492 * 2 ^ 59
def prefixEnd_6241492 : Nat := 4983230072969 + 3 ^ 40 * 6241492 * 2
def baseEnd_6241492 : Nat := 118699459155266643242441

theorem tailTrace_6241492 : CollatzResearch.WordTrace tailWord_6241492 prefixEnd_6241492 118699459155266643242441 := by
  unfold tailWord_6241492
  simp only [CollatzResearch.WordTrace]
  refine ⟨113822957552073960406571365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151763943402765280542095153 113822957552073960406571365)
  ·
    refine ⟨21341804541013867576232131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113822957552073960406571365 21341804541013867576232131)
    ·
      refine ⟨32012706811520801364348197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341804541013867576232131 32012706811520801364348197)
      ·
        refine ⟨6002382527160150255815287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32012706811520801364348197 6002382527160150255815287)
        ·
          refine ⟨9003573790740225383722931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002382527160150255815287 9003573790740225383722931)
          ·
            refine ⟨13505360686110338075584397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003573790740225383722931 13505360686110338075584397)
            ·
              refine ⟨5064510257291376778344149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13505360686110338075584397 5064510257291376778344149)
              ·
                refine ⟨118699459155266643242441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5064510257291376778344149 118699459155266643242441)
                ·
                  rfl

theorem cell23_6241492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 7].length) (baseStart_6241492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241492 prefixEnd_6241492 := by exact prefixLift 6241492
  have htrace : WordTrace (prefixWord ++ tailWord_6241492) baseStart_6241492 baseEnd_6241492 := by
    simpa [prefixWord, tailWord_6241492, baseEnd_6241492] using wordTrace_append hprefix tailTrace_6241492
  have hstable : (prefixWord ++ tailWord_6241492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241492).length < 2 ^ (prefixWord ++ tailWord_6241492).sum := by decide
  have hdescent : baseEnd_6241492 < baseStart_6241492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241495 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_6241495 : Nat := 118140960795 + 6241495 * 2 ^ 59
def prefixEnd_6241495 : Nat := 4983230072969 + 3 ^ 40 * 6241495 * 2
def baseEnd_6241495 : Nat := 3204886937634162855808393

theorem tailTrace_6241495 : CollatzResearch.WordTrace tailWord_6241495 prefixEnd_6241495 3204886937634162855808393 := by
  unfold tailWord_6241495
  simp only [CollatzResearch.WordTrace]
  refine ⟨227646024523137052325501939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151764016348758034883667959 227646024523137052325501939)
  ·
    refine ⟨341469036784705578488252909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227646024523137052325501939 341469036784705578488252909)
    ·
      refine ⟨128050888794264591933094841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341469036784705578488252909 128050888794264591933094841)
      ·
        refine ⟨96038166595698443949821131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128050888794264591933094841 96038166595698443949821131)
        ·
          refine ⟨144057249893547665924731697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96038166595698443949821131 144057249893547665924731697)
          ·
            refine ⟨108042937420160749443548773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144057249893547665924731697 108042937420160749443548773)
            ·
              refine ⟨20258050766280140520665395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108042937420160749443548773 20258050766280140520665395)
              ·
                refine ⟨30387076149420210780998093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20258050766280140520665395 30387076149420210780998093)
                ·
                  refine ⟨11395153556032579042874285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30387076149420210780998093 11395153556032579042874285)
                  ·
                    refine ⟨4273182583512217141077857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11395153556032579042874285 4273182583512217141077857)
                    ·
                      refine ⟨3204886937634162855808393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273182583512217141077857 3204886937634162855808393)
                      ·
                        rfl

theorem cell23_6241495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_6241495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241495 prefixEnd_6241495 := by exact prefixLift 6241495
  have htrace : WordTrace (prefixWord ++ tailWord_6241495) baseStart_6241495 baseEnd_6241495 := by
    simpa [prefixWord, tailWord_6241495, baseEnd_6241495] using wordTrace_append hprefix tailTrace_6241495
  have hstable : (prefixWord ++ tailWord_6241495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241495).length < 2 ^ (prefixWord ++ tailWord_6241495).sum := by decide
  have hdescent : baseEnd_6241495 < baseStart_6241495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241512 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6241512 : Nat := 118140960795 + 6241512 * 2 ^ 59
def prefixEnd_6241512 : Nat := 4983230072969 + 3 ^ 40 * 6241512 * 2
def baseEnd_6241512 : Nat := 3204895666805289289295815

theorem tailTrace_6241512 : CollatzResearch.WordTrace tailWord_6241512 prefixEnd_6241512 3204895666805289289295815 := by
  unfold tailWord_6241512
  simp only [CollatzResearch.WordTrace]
  refine ⟨113823322282037732114435395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151764429709383642819247193 113823322282037732114435395)
  ·
    refine ⟨170734983423056598171653093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113823322282037732114435395 170734983423056598171653093)
    ·
      refine ⟨32012809391823112157184955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170734983423056598171653093 32012809391823112157184955)
      ·
        refine ⟨48019214087734668235777433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32012809391823112157184955 48019214087734668235777433)
        ·
          refine ⟨36014410565801001176833075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48019214087734668235777433 36014410565801001176833075)
          ·
            refine ⟨54021615848701501765249613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36014410565801001176833075 54021615848701501765249613)
            ·
              refine ⟨20258105943263063161968605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54021615848701501765249613 20258105943263063161968605)
              ·
                refine ⟨7596789728723648685738227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20258105943263063161968605 7596789728723648685738227)
                ·
                  refine ⟨11395184593085473028607341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596789728723648685738227 11395184593085473028607341)
                  ·
                    refine ⟨4273194222407052385727753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11395184593085473028607341 4273194222407052385727753)
                    ·
                      refine ⟨3204895666805289289295815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273194222407052385727753 3204895666805289289295815)
                      ·
                        rfl

theorem cell23_6241512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6241512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241512 prefixEnd_6241512 := by exact prefixLift 6241512
  have htrace : WordTrace (prefixWord ++ tailWord_6241512) baseStart_6241512 baseEnd_6241512 := by
    simpa [prefixWord, tailWord_6241512, baseEnd_6241512] using wordTrace_append hprefix tailTrace_6241512
  have hstable : (prefixWord ++ tailWord_6241512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241512).length < 2 ^ (prefixWord ++ tailWord_6241512).sum := by decide
  have hdescent : baseEnd_6241512 < baseStart_6241512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241518 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6241518 : Nat := 118140960795 + 6241518 * 2 ^ 59
def prefixEnd_6241518 : Nat := 4983230072969 + 3 ^ 40 * 6241518 * 2
def baseEnd_6241518 : Nat := 1068299582563072088606929

theorem tailTrace_6241518 : CollatzResearch.WordTrace tailWord_6241518 prefixEnd_6241518 1068299582563072088606929 := by
  unfold tailWord_6241518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455857925256715906698651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151764575601369151502392805 28455857925256715906698651)
  ·
    refine ⟨42683786887885073860047977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28455857925256715906698651 42683786887885073860047977)
    ·
      refine ⟨32012840165913805395035983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42683786887885073860047977 32012840165913805395035983)
      ·
        refine ⟨48019260248870708092553975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32012840165913805395035983 48019260248870708092553975)
        ·
          refine ⟨72028890373306062138830963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48019260248870708092553975 72028890373306062138830963)
          ·
            refine ⟨108043335559959093208246445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72028890373306062138830963 108043335559959093208246445)
            ·
              refine ⟨40516250834984659953092417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108043335559959093208246445 40516250834984659953092417)
              ·
                refine ⟨30387188126238494964819313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40516250834984659953092417 30387188126238494964819313)
                ·
                  refine ⟨22790391094678871223614485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30387188126238494964819313 22790391094678871223614485)
                  ·
                    refine ⟨1068299582563072088606929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22790391094678871223614485 1068299582563072088606929)
                    ·
                      rfl

theorem cell23_6241518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6241518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241518 prefixEnd_6241518 := by exact prefixLift 6241518
  have htrace : WordTrace (prefixWord ++ tailWord_6241518) baseStart_6241518 baseEnd_6241518 := by
    simpa [prefixWord, tailWord_6241518, baseEnd_6241518] using wordTrace_append hprefix tailTrace_6241518
  have hstable : (prefixWord ++ tailWord_6241518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241518).length < 2 ^ (prefixWord ++ tailWord_6241518).sum := by decide
  have hdescent : baseEnd_6241518 < baseStart_6241518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241519 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_6241519 : Nat := 118140960795 + 6241519 * 2 ^ 59
def prefixEnd_6241519 : Nat := 4983230072969 + 3 ^ 40 * 6241519 * 2
def baseEnd_6241519 : Nat := 3204899261169870761908283

theorem tailTrace_6241519 : CollatzResearch.WordTrace tailWord_6241519 prefixEnd_6241519 3204899261169870761908283 := by
  unfold tailWord_6241519
  simp only [CollatzResearch.WordTrace]
  refine ⟨227646899875050104424375611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151764599916700069616250407 227646899875050104424375611)
  ·
    refine ⟨341470349812575156636563417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227646899875050104424375611 341470349812575156636563417)
    ·
      refine ⟨256102762359431367477422563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341470349812575156636563417 256102762359431367477422563)
      ·
        refine ⟨384154143539147051216133845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256102762359431367477422563 384154143539147051216133845)
        ·
          refine ⟨9003612739198759012878137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 384154143539147051216133845 9003612739198759012878137)
          ·
            refine ⟨6752709554399069259658603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003612739198759012878137 6752709554399069259658603)
            ·
              refine ⟨10129064331598603889487905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752709554399069259658603 10129064331598603889487905)
              ·
                refine ⟨7596798248698952917115929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10129064331598603889487905 7596798248698952917115929)
                ·
                  refine ⟨5697598686524214687836947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596798248698952917115929 5697598686524214687836947)
                  ·
                    refine ⟨8546398029786322031755421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697598686524214687836947 8546398029786322031755421)
                    ·
                      refine ⟨3204899261169870761908283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546398029786322031755421 3204899261169870761908283)
                      ·
                        rfl

theorem cell23_6241519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_6241519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241519 prefixEnd_6241519 := by exact prefixLift 6241519
  have htrace : WordTrace (prefixWord ++ tailWord_6241519) baseStart_6241519 baseEnd_6241519 := by
    simpa [prefixWord, tailWord_6241519, baseEnd_6241519] using wordTrace_append hprefix tailTrace_6241519
  have hstable : (prefixWord ++ tailWord_6241519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241519).length < 2 ^ (prefixWord ++ tailWord_6241519).sum := by decide
  have hdescent : baseEnd_6241519 < baseStart_6241519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241548 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 7]
def baseStart_6241548 : Nat := 118140960795 + 6241548 * 2 ^ 59
def prefixEnd_6241548 : Nat := 4983230072969 + 3 ^ 40 * 6241548 * 2
def baseEnd_6241548 : Nat := 356101572456539016493961

theorem tailTrace_6241548 : CollatzResearch.WordTrace tailWord_6241548 prefixEnd_6241548 356101572456539016493961 := by
  unfold tailWord_6241548
  simp only [CollatzResearch.WordTrace]
  refine ⟨113823978795972521188590649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151765305061296694918120865 113823978795972521188590649)
  ·
    refine ⟨85367984096979390891442987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113823978795972521188590649 85367984096979390891442987)
    ·
      refine ⟨128051976145469086337164481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85367984096979390891442987 128051976145469086337164481)
      ·
        refine ⟨96038982109101814752873361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128051976145469086337164481 96038982109101814752873361)
        ·
          refine ⟨72029236581826361064655021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96038982109101814752873361 72029236581826361064655021)
          ·
            refine ⟨27010963718184885399245633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72029236581826361064655021 27010963718184885399245633)
            ·
              refine ⟨20258222788638664049434225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27010963718184885399245633 20258222788638664049434225)
              ·
                refine ⟨15193667091478998037075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20258222788638664049434225 15193667091478998037075669)
                ·
                  refine ⟨356101572456539016493961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15193667091478998037075669 356101572456539016493961)
                  ·
                    rfl

theorem cell23_6241548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_6241548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241548 prefixEnd_6241548 := by exact prefixLift 6241548
  have htrace : WordTrace (prefixWord ++ tailWord_6241548) baseStart_6241548 baseEnd_6241548 := by
    simpa [prefixWord, tailWord_6241548, baseEnd_6241548] using wordTrace_append hprefix tailTrace_6241548
  have hstable : (prefixWord ++ tailWord_6241548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241548).length < 2 ^ (prefixWord ++ tailWord_6241548).sum := by decide
  have hdescent : baseEnd_6241548 < baseStart_6241548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241593 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6241593 : Nat := 118140960795 + 6241593 * 2 ^ 59
def prefixEnd_6241593 : Nat := 4983230072969 + 3 ^ 40 * 6241593 * 2
def baseEnd_6241593 : Nat := 3204937258738303472382943

theorem tailTrace_6241593 : CollatzResearch.WordTrace tailWord_6241593 prefixEnd_6241593 3204937258738303472382943 := by
  unfold tailWord_6241593
  simp only [CollatzResearch.WordTrace]
  refine ⟨227649598876782015062569433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151766399251188010041712955 227649598876782015062569433)
  ·
    refine ⟨170737199157586511296927075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227649598876782015062569433 170737199157586511296927075)
    ·
      refine ⟨256105798736379766945390613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170737199157586511296927075 256105798736379766945390613)
      ·
        refine ⟨12004959315767801575565185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256105798736379766945390613 12004959315767801575565185)
        ·
          refine ⟨9003719486825851181673889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12004959315767801575565185 9003719486825851181673889)
          ·
            refine ⟨6752789615119388386255417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003719486825851181673889 6752789615119388386255417)
            ·
              refine ⟨5064592211339541289691563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6752789615119388386255417 5064592211339541289691563)
              ·
                refine ⟨7596888317009311934537345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064592211339541289691563 7596888317009311934537345)
                ·
                  refine ⟨5697666237756983950903009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596888317009311934537345 5697666237756983950903009)
                  ·
                    refine ⟨4273249678317737963177257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5697666237756983950903009 4273249678317737963177257)
                    ·
                      refine ⟨3204937258738303472382943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273249678317737963177257 3204937258738303472382943)
                      ·
                        rfl

theorem cell23_6241593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6241593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241593 prefixEnd_6241593 := by exact prefixLift 6241593
  have htrace : WordTrace (prefixWord ++ tailWord_6241593) baseStart_6241593 baseEnd_6241593 := by
    simpa [prefixWord, tailWord_6241593, baseEnd_6241593] using wordTrace_append hprefix tailTrace_6241593
  have hstable : (prefixWord ++ tailWord_6241593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241593).length < 2 ^ (prefixWord ++ tailWord_6241593).sum := by decide
  have hdescent : baseEnd_6241593 < baseStart_6241593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241658 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_6241658 : Nat := 118140960795 + 6241658 * 2 ^ 59
def prefixEnd_6241658 : Nat := 4983230072969 + 3 ^ 40 * 6241658 * 2
def baseEnd_6241658 : Nat := 3204970634980845718070143

theorem tailTrace_6241658 : CollatzResearch.WordTrace tailWord_6241658 prefixEnd_6241658 3204970634980845718070143 := by
  unfold tailWord_6241658
  simp only [CollatzResearch.WordTrace]
  refine ⟨56912992405386632790921407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151767979747697687442457085 56912992405386632790921407)
  ·
    refine ⟨85369488608079949186382111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56912992405386632790921407 85369488608079949186382111)
    ·
      refine ⟨128054232912119923779573167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85369488608079949186382111 128054232912119923779573167)
      ·
        refine ⟨192081349368179885669359751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128054232912119923779573167 192081349368179885669359751)
        ·
          refine ⟨288122024052269828504039627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192081349368179885669359751 288122024052269828504039627)
          ·
            refine ⟨432183036078404742756059441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288122024052269828504039627 432183036078404742756059441)
            ·
              refine ⟨324137277058803557067044581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432183036078404742756059441 324137277058803557067044581)
              ·
                refine ⟨60775739448525666950070859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324137277058803557067044581 60775739448525666950070859)
                ·
                  refine ⟨91163609172788500425106289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60775739448525666950070859 91163609172788500425106289)
                  ·
                    refine ⟨68372706879591375318829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91163609172788500425106289 68372706879591375318829717)
                    ·
                      refine ⟨3204970634980845718070143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68372706879591375318829717 3204970634980845718070143)
                      ·
                        rfl

theorem cell23_6241658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_6241658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241658 prefixEnd_6241658 := by exact prefixLift 6241658
  have htrace : WordTrace (prefixWord ++ tailWord_6241658) baseStart_6241658 baseEnd_6241658 := by
    simpa [prefixWord, tailWord_6241658, baseEnd_6241658] using wordTrace_append hprefix tailTrace_6241658
  have hstable : (prefixWord ++ tailWord_6241658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241658).length < 2 ^ (prefixWord ++ tailWord_6241658).sum := by decide
  have hdescent : baseEnd_6241658 < baseStart_6241658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241666 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6241666 : Nat := 118140960795 + 6241666 * 2 ^ 59
def prefixEnd_6241666 : Nat := 4983230072969 + 3 ^ 40 * 6241666 * 2
def baseEnd_6241666 : Nat := 3204974742826081686770107

theorem tailTrace_6241666 : CollatzResearch.WordTrace tailWord_6241666 prefixEnd_6241666 3204974742826081686770107 := by
  unfold tailWord_6241666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913065351379387132494213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151768174270345032353317901 56913065351379387132494213)
  ·
    refine ⟨10671199753383635087342665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56913065351379387132494213 10671199753383635087342665)
    ·
      refine ⟨8003399815037726315506999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10671199753383635087342665 8003399815037726315506999)
      ·
        refine ⟨12005099722556589473260499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003399815037726315506999 12005099722556589473260499)
        ·
          refine ⟨18007649583834884209890749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005099722556589473260499 18007649583834884209890749)
          ·
            refine ⟨6752868593938081578709031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18007649583834884209890749 6752868593938081578709031)
            ·
              refine ⟨10129302890907122368063547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752868593938081578709031 10129302890907122368063547)
              ·
                refine ⟨15193954336360683552095321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129302890907122368063547 15193954336360683552095321)
                ·
                  refine ⟨11395465752270512664071491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15193954336360683552095321 11395465752270512664071491)
                  ·
                    refine ⟨17093198628405768996107237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11395465752270512664071491 17093198628405768996107237)
                    ·
                      refine ⟨3204974742826081686770107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17093198628405768996107237 3204974742826081686770107)
                      ·
                        rfl

theorem cell23_6241666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6241666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241666 prefixEnd_6241666 := by exact prefixLift 6241666
  have htrace : WordTrace (prefixWord ++ tailWord_6241666) baseStart_6241666 baseEnd_6241666 := by
    simpa [prefixWord, tailWord_6241666, baseEnd_6241666] using wordTrace_append hprefix tailTrace_6241666
  have hstable : (prefixWord ++ tailWord_6241666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241666).length < 2 ^ (prefixWord ++ tailWord_6241666).sum := by decide
  have hdescent : baseEnd_6241666 < baseStart_6241666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241699 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 1, 1, 3]
def baseStart_6241699 : Nat := 118140960795 + 6241699 * 2 ^ 59
def prefixEnd_6241699 : Nat := 4983230072969 + 3 ^ 40 * 6241699 * 2
def baseEnd_6241699 : Nat := 3204991687687680057657455

theorem tailTrace_6241699 : CollatzResearch.WordTrace tailWord_6241699 prefixEnd_6241699 3204991687687680057657455 := by
  unfold tailWord_6241699
  simp only [CollatzResearch.WordTrace]
  refine ⟨227653465014397995165928151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151768976676265330110618767 227653465014397995165928151)
  ·
    refine ⟨341480197521596992748892227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227653465014397995165928151 341480197521596992748892227)
    ·
      refine ⟨512220296282395489123338341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341480197521596992748892227 512220296282395489123338341)
      ·
        refine ⟨96041305552949154210625939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512220296282395489123338341 96041305552949154210625939)
        ·
          refine ⟨144061958329423731315938909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96041305552949154210625939 144061958329423731315938909)
          ·
            refine ⟨54023234373533899243477091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144061958329423731315938909 54023234373533899243477091)
            ·
              refine ⟨81034851560300848865215637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54023234373533899243477091 81034851560300848865215637)
              ·
                refine ⟨3798508666889102290556983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81034851560300848865215637 3798508666889102290556983)
                ·
                  refine ⟨5697763000333653435835475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798508666889102290556983 5697763000333653435835475)
                  ·
                    refine ⟨8546644500500480153753213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697763000333653435835475 8546644500500480153753213)
                    ·
                      refine ⟨3204991687687680057657455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546644500500480153753213 3204991687687680057657455)
                      ·
                        rfl

theorem cell23_6241699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_6241699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241699 prefixEnd_6241699 := by exact prefixLift 6241699
  have htrace : WordTrace (prefixWord ++ tailWord_6241699) baseStart_6241699 baseEnd_6241699 := by
    simpa [prefixWord, tailWord_6241699, baseEnd_6241699] using wordTrace_append hprefix tailTrace_6241699
  have hstable : (prefixWord ++ tailWord_6241699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241699).length < 2 ^ (prefixWord ++ tailWord_6241699).sum := by decide
  have hdescent : baseEnd_6241699 < baseStart_6241699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241709 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6241709 : Nat := 118140960795 + 6241709 * 2 ^ 59
def prefixEnd_6241709 : Nat := 4983230072969 + 3 ^ 40 * 6241709 * 2
def baseEnd_6241709 : Nat := 3204996822494225018532409

theorem tailTrace_6241709 : CollatzResearch.WordTrace tailWord_6241709 prefixEnd_6241709 3204996822494225018532409 := by
  unfold tailWord_6241709
  simp only [CollatzResearch.WordTrace]
  refine ⟨227653829744361766873792181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151769219829574511249194787 227653829744361766873792181)
  ·
    refine ⟨21342546538533915644418017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227653829744361766873792181 21342546538533915644418017)
    ·
      refine ⟨16006909903900436733313513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21342546538533915644418017 16006909903900436733313513)
      ·
        refine ⟨12005182427925327549985135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16006909903900436733313513 12005182427925327549985135)
        ·
          refine ⟨18007773641887991324977703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005182427925327549985135 18007773641887991324977703)
          ·
            refine ⟨27011660462831986987466555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007773641887991324977703 27011660462831986987466555)
            ·
              refine ⟨40517490694247980481199833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27011660462831986987466555 40517490694247980481199833)
              ·
                refine ⟨30388118020685985360899875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40517490694247980481199833 30388118020685985360899875)
                ·
                  refine ⟨45582177031028978041349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30388118020685985360899875 45582177031028978041349813)
                  ·
                    refine ⟨4273329096658966691376545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45582177031028978041349813 4273329096658966691376545)
                    ·
                      refine ⟨3204996822494225018532409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273329096658966691376545 3204996822494225018532409)
                      ·
                        rfl

theorem cell23_6241709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6241709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241709 prefixEnd_6241709 := by exact prefixLift 6241709
  have htrace : WordTrace (prefixWord ++ tailWord_6241709) baseStart_6241709 baseEnd_6241709 := by
    simpa [prefixWord, tailWord_6241709, baseEnd_6241709] using wordTrace_append hprefix tailTrace_6241709
  have hstable : (prefixWord ++ tailWord_6241709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241709).length < 2 ^ (prefixWord ++ tailWord_6241709).sum := by decide
  have hdescent : baseEnd_6241709 < baseStart_6241709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241725 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_6241725 : Nat := 118140960795 + 6241725 * 2 ^ 59
def prefixEnd_6241725 : Nat := 4983230072969 + 3 ^ 40 * 6241725 * 2
def baseEnd_6241725 : Nat := 3205005038184696955932335

theorem tailTrace_6241725 : CollatzResearch.WordTrace tailWord_6241725 prefixEnd_6241725 3205005038184696955932335 := by
  unfold tailWord_6241725
  simp only [CollatzResearch.WordTrace]
  refine ⟨227654413312303801606374629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151769608874869201070916419 227654413312303801606374629)
  ·
    refine ⟨42685202496056962801195243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227654413312303801606374629 42685202496056962801195243)
    ·
      refine ⟨64027803744085444201792865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42685202496056962801195243 64027803744085444201792865)
      ·
        refine ⟨48020852808064083151344649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64027803744085444201792865 48020852808064083151344649)
        ·
          refine ⟨36015639606048062363508487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48020852808064083151344649 36015639606048062363508487)
          ·
            refine ⟨54023459409072093545262731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36015639606048062363508487 54023459409072093545262731)
            ·
              refine ⟨81035189113608140317894097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54023459409072093545262731 81035189113608140317894097)
              ·
                refine ⟨60776391835206105238420573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81035189113608140317894097 60776391835206105238420573)
                ·
                  refine ⟨22791146938202289464407715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60776391835206105238420573 22791146938202289464407715)
                  ·
                    refine ⟨34186720407303434196611573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22791146938202289464407715 34186720407303434196611573)
                    ·
                      refine ⟨3205005038184696955932335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34186720407303434196611573 3205005038184696955932335)
                      ·
                        rfl

theorem cell23_6241725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_6241725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241725 prefixEnd_6241725 := by exact prefixLift 6241725
  have htrace : WordTrace (prefixWord ++ tailWord_6241725) baseStart_6241725 baseEnd_6241725 := by
    simpa [prefixWord, tailWord_6241725, baseEnd_6241725] using wordTrace_append hprefix tailTrace_6241725
  have hstable : (prefixWord ++ tailWord_6241725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241725).length < 2 ^ (prefixWord ++ tailWord_6241725).sum := by decide
  have hdescent : baseEnd_6241725 < baseStart_6241725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241735 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_6241735 : Nat := 118140960795 + 6241735 * 2 ^ 59
def prefixEnd_6241735 : Nat := 4983230072969 + 3 ^ 40 * 6241735 * 2
def baseEnd_6241735 : Nat := 3205010172991241916807289

theorem tailTrace_6241735 : CollatzResearch.WordTrace tailWord_6241735 prefixEnd_6241735 3205010172991241916807289 := by
  unfold tailWord_6241735
  simp only [CollatzResearch.WordTrace]
  refine ⟨227654778042267573314238659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151769852028178382209492439 227654778042267573314238659)
  ·
    refine ⟨341482167063401359971357989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227654778042267573314238659 341482167063401359971357989)
    ·
      refine ⟨64027906324387754994629623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341482167063401359971357989 64027906324387754994629623)
      ·
        refine ⟨96041859486581632491944435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64027906324387754994629623 96041859486581632491944435)
        ·
          refine ⟨144062789229872448737916653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96041859486581632491944435 144062789229872448737916653)
          ·
            refine ⟨54023545961202168276718745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144062789229872448737916653 54023545961202168276718745)
            ·
              refine ⟨40517659470901626207539059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54023545961202168276718745 40517659470901626207539059)
              ·
                refine ⟨60776489206352439311308589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40517659470901626207539059 60776489206352439311308589)
                ·
                  refine ⟨22791183452382164741740721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60776489206352439311308589 22791183452382164741740721)
                  ·
                    refine ⟨17093387589286623556305541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22791183452382164741740721 17093387589286623556305541)
                    ·
                      refine ⟨3205010172991241916807289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17093387589286623556305541 3205010172991241916807289)
                      ·
                        rfl

theorem cell23_6241735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_6241735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241735 prefixEnd_6241735 := by exact prefixLift 6241735
  have htrace : WordTrace (prefixWord ++ tailWord_6241735) baseStart_6241735 baseEnd_6241735 := by
    simpa [prefixWord, tailWord_6241735, baseEnd_6241735] using wordTrace_append hprefix tailTrace_6241735
  have hstable : (prefixWord ++ tailWord_6241735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241735).length < 2 ^ (prefixWord ++ tailWord_6241735).sum := by decide
  have hdescent : baseEnd_6241735 < baseStart_6241735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241750 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6241750 : Nat := 118140960795 + 6241750 * 2 ^ 59
def prefixEnd_6241750 : Nat := 4983230072969 + 3 ^ 40 * 6241750 * 2
def baseEnd_6241750 : Nat := 3205017875201059358119721

theorem tailTrace_6241750 : CollatzResearch.WordTrace tailWord_6241750 prefixEnd_6241750 3205017875201059358119721 := by
  unfold tailWord_6241750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228457821075826929752169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151770216758142153917356469 14228457821075826929752169)
  ·
    refine ⟨10671343365806870197314127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14228457821075826929752169 10671343365806870197314127)
    ·
      refine ⟨16007015048710305295971191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671343365806870197314127 16007015048710305295971191)
      ·
        refine ⟨24010522573065457943956787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16007015048710305295971191 24010522573065457943956787)
        ·
          refine ⟨36015783859598186915935181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24010522573065457943956787 36015783859598186915935181)
          ·
            refine ⟨13505918947349320093475693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36015783859598186915935181 13505918947349320093475693)
            ·
              refine ⟨5064719605255995035053385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13505918947349320093475693 5064719605255995035053385)
              ·
                refine ⟨3798539703941996276290039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064719605255995035053385 3798539703941996276290039)
                ·
                  refine ⟨5697809555912994414435059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798539703941996276290039 5697809555912994414435059)
                  ·
                    refine ⟨8546714333869491621652589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697809555912994414435059 8546714333869491621652589)
                    ·
                      refine ⟨3205017875201059358119721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546714333869491621652589 3205017875201059358119721)
                      ·
                        rfl

theorem cell23_6241750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6241750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241750 prefixEnd_6241750 := by exact prefixLift 6241750
  have htrace : WordTrace (prefixWord ++ tailWord_6241750) baseStart_6241750 baseEnd_6241750 := by
    simpa [prefixWord, tailWord_6241750, baseEnd_6241750] using wordTrace_append hprefix tailTrace_6241750
  have hstable : (prefixWord ++ tailWord_6241750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241750).length < 2 ^ (prefixWord ++ tailWord_6241750).sum := by decide
  have hdescent : baseEnd_6241750 < baseStart_6241750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241772 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_6241772 : Nat := 118140960795 + 6241772 * 2 ^ 59
def prefixEnd_6241772 : Nat := 4983230072969 + 3 ^ 40 * 6241772 * 2
def baseEnd_6241772 : Nat := 3205029171775458272044619

theorem tailTrace_6241772 : CollatzResearch.WordTrace tailWord_6241772 prefixEnd_6241772 3205029171775458272044619 := by
  unfold tailWord_6241772
  simp only [CollatzResearch.WordTrace]
  refine ⟨113828063771566764316667785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151770751695422352422223713 113828063771566764316667785)
  ·
    refine ⟨85371047828675073237500839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113828063771566764316667785 85371047828675073237500839)
    ·
      refine ⟨128056571743012609856251259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85371047828675073237500839 128056571743012609856251259)
      ·
        refine ⟨192084857614518914784376889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128056571743012609856251259 192084857614518914784376889)
        ·
          refine ⟨144063643210889186088282667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192084857614518914784376889 144063643210889186088282667)
          ·
            refine ⟨216095464816333779132424001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144063643210889186088282667 216095464816333779132424001)
            ·
              refine ⟨162071598612250334349318001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216095464816333779132424001 162071598612250334349318001)
              ·
                refine ⟨121553698959187750761988501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162071598612250334349318001 121553698959187750761988501)
                ·
                  refine ⟨5697829638711925816968211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121553698959187750761988501 5697829638711925816968211)
                  ·
                    refine ⟨8546744458067888725452317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697829638711925816968211 8546744458067888725452317)
                    ·
                      refine ⟨3205029171775458272044619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546744458067888725452317 3205029171775458272044619)
                      ·
                        rfl

theorem cell23_6241772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_6241772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241772 prefixEnd_6241772 := by exact prefixLift 6241772
  have htrace : WordTrace (prefixWord ++ tailWord_6241772) baseStart_6241772 baseEnd_6241772 := by
    simpa [prefixWord, tailWord_6241772, baseEnd_6241772] using wordTrace_append hprefix tailTrace_6241772
  have hstable : (prefixWord ++ tailWord_6241772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241772).length < 2 ^ (prefixWord ++ tailWord_6241772).sum := by decide
  have hdescent : baseEnd_6241772 < baseStart_6241772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241773 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6241773 : Nat := 118140960795 + 6241773 * 2 ^ 59
def prefixEnd_6241773 : Nat := 4983230072969 + 3 ^ 40 * 6241773 * 2
def baseEnd_6241773 : Nat := 3205029685256112768132115

theorem tailTrace_6241773 : CollatzResearch.WordTrace tailWord_6241773 prefixEnd_6241773 3205029685256112768132115 := by
  unfold tailWord_6241773
  simp only [CollatzResearch.WordTrace]
  refine ⟨227656164016129905804121973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151770776010753270536081315 227656164016129905804121973)
  ·
    refine ⟨21342765376512178669136435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227656164016129905804121973 21342765376512178669136435)
    ·
      refine ⟨32014148064768268003704653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342765376512178669136435 32014148064768268003704653)
      ·
        refine ⟨12005305524288100501389245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32014148064768268003704653 12005305524288100501389245)
        ·
          refine ⟨4501989571608037688020967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12005305524288100501389245 4501989571608037688020967)
          ·
            refine ⟨6752984357412056532031451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501989571608037688020967 6752984357412056532031451)
            ·
              refine ⟨10129476536118084798047177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752984357412056532031451 10129476536118084798047177)
              ·
                refine ⟨7597107402088563598535383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10129476536118084798047177 7597107402088563598535383)
                ·
                  refine ⟨11395661103132845397803075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597107402088563598535383 11395661103132845397803075)
                  ·
                    refine ⟨17093491654699268096704613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11395661103132845397803075 17093491654699268096704613)
                    ·
                      refine ⟨3205029685256112768132115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17093491654699268096704613 3205029685256112768132115)
                      ·
                        rfl

theorem cell23_6241773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6241773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241773 prefixEnd_6241773 := by exact prefixLift 6241773
  have htrace : WordTrace (prefixWord ++ tailWord_6241773) baseStart_6241773 baseEnd_6241773 := by
    simpa [prefixWord, tailWord_6241773, baseEnd_6241773] using wordTrace_append hprefix tailTrace_6241773
  have hstable : (prefixWord ++ tailWord_6241773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241773).length < 2 ^ (prefixWord ++ tailWord_6241773).sum := by decide
  have hdescent : baseEnd_6241773 < baseStart_6241773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241829 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_6241829 : Nat := 118140960795 + 6241829 * 2 ^ 59
def prefixEnd_6241829 : Nat := 4983230072969 + 3 ^ 40 * 6241829 * 2
def baseEnd_6241829 : Nat := 3205058440172764549031857

theorem tailTrace_6241829 : CollatzResearch.WordTrace tailWord_6241829 prefixEnd_6241829 3205058440172764549031857 := by
  unfold tailWord_6241829
  simp only [CollatzResearch.WordTrace]
  refine ⟨227658206503927027368160541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151772137669284684912107027 227658206503927027368160541)
  ·
    refine ⟨85371827438972635263060203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227658206503927027368160541 85371827438972635263060203)
    ·
      refine ⟨128057741158458952894590305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85371827438972635263060203 128057741158458952894590305)
      ·
        refine ⟨96043305868844214670942729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128057741158458952894590305 96043305868844214670942729)
        ·
          refine ⟨72032479401633161003207047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96043305868844214670942729 72032479401633161003207047)
          ·
            refine ⟨108048719102449741504810571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72032479401633161003207047 108048719102449741504810571)
            ·
              refine ⟨162073078653674612257215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108048719102449741504810571 162073078653674612257215857)
              ·
                refine ⟨121554808990255959192911893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162073078653674612257215857 121554808990255959192911893)
                ·
                  refine ⟨5697881671418248087167745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121554808990255959192911893 5697881671418248087167745)
                  ·
                    refine ⟨4273411253563686065375809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5697881671418248087167745 4273411253563686065375809)
                    ·
                      refine ⟨3205058440172764549031857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273411253563686065375809 3205058440172764549031857)
                      ·
                        rfl

theorem cell23_6241829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_6241829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241829 prefixEnd_6241829 := by exact prefixLift 6241829
  have htrace : WordTrace (prefixWord ++ tailWord_6241829) baseStart_6241829 baseEnd_6241829 := by
    simpa [prefixWord, tailWord_6241829, baseEnd_6241829] using wordTrace_append hprefix tailTrace_6241829
  have hstable : (prefixWord ++ tailWord_6241829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241829).length < 2 ^ (prefixWord ++ tailWord_6241829).sum := by decide
  have hdescent : baseEnd_6241829 < baseStart_6241829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241929 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_6241929 : Nat := 118140960795 + 6241929 * 2 ^ 59
def prefixEnd_6241929 : Nat := 4983230072969 + 3 ^ 40 * 6241929 * 2
def baseEnd_6241929 : Nat := 1068369929412738052593799

theorem tailTrace_6241929 : CollatzResearch.WordTrace tailWord_6241929 prefixEnd_6241929 1068369929412738052593799 := by
  unfold tailWord_6241929
  simp only [CollatzResearch.WordTrace]
  refine ⟨227661853803564744446800841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151774569202376496297867227 227661853803564744446800841)
  ·
    refine ⟨170746390352673558335100631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227661853803564744446800841 170746390352673558335100631)
    ·
      refine ⟨256119585529010337502650947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170746390352673558335100631 256119585529010337502650947)
      ·
        refine ⟨384179378293515506253976421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256119585529010337502650947 384179378293515506253976421)
        ·
          refine ⟨72033633430034157422620579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384179378293515506253976421 72033633430034157422620579)
          ·
            refine ⟨108050450145051236133930869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72033633430034157422620579 108050450145051236133930869)
            ·
              refine ⟨10129729701098553387556019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108050450145051236133930869 10129729701098553387556019)
              ·
                refine ⟨15194594551647830081334029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129729701098553387556019 15194594551647830081334029)
                ·
                  refine ⟨5697972956867936280500261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15194594551647830081334029 5697972956867936280500261)
                  ·
                    refine ⟨1068369929412738052593799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697972956867936280500261 1068369929412738052593799)
                    ·
                      rfl

theorem cell23_6241929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_6241929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241929 prefixEnd_6241929 := by exact prefixLift 6241929
  have htrace : WordTrace (prefixWord ++ tailWord_6241929) baseStart_6241929 baseEnd_6241929 := by
    simpa [prefixWord, tailWord_6241929, baseEnd_6241929] using wordTrace_append hprefix tailTrace_6241929
  have hstable : (prefixWord ++ tailWord_6241929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241929).length < 2 ^ (prefixWord ++ tailWord_6241929).sum := by decide
  have hdescent : baseEnd_6241929 < baseStart_6241929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241956 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_6241956 : Nat := 118140960795 + 6241956 * 2 ^ 59
def prefixEnd_6241956 : Nat := 4983230072969 + 3 ^ 40 * 6241956 * 2
def baseEnd_6241956 : Nat := 3205123652215885552143773

theorem tailTrace_6241956 : CollatzResearch.WordTrace tailWord_6241956 prefixEnd_6241956 3205123652215885552143773 := by
  unfold tailWord_6241956
  simp only [CollatzResearch.WordTrace]
  refine ⟨113831419287233464029016861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151775225716311285372022481 113831419287233464029016861)
  ·
    refine ⟨42686782232712549010881323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113831419287233464029016861 42686782232712549010881323)
    ·
      refine ⟨64030173349068823516321985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686782232712549010881323 64030173349068823516321985)
      ·
        refine ⟨48022630011801617637241489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64030173349068823516321985 48022630011801617637241489)
        ·
          refine ⟨36016972508851213227931117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48022630011801617637241489 36016972508851213227931117)
          ·
            refine ⟨13506364690819204960474169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36016972508851213227931117 13506364690819204960474169)
            ·
              refine ⟨10129773518114403720355627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13506364690819204960474169 10129773518114403720355627)
              ·
                refine ⟨15194660277171605580533441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129773518114403720355627 15194660277171605580533441)
                ·
                  refine ⟨11395995207878704185400081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15194660277171605580533441 11395995207878704185400081)
                  ·
                    refine ⟨8546996405909028139050061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11395995207878704185400081 8546996405909028139050061)
                    ·
                      refine ⟨3205123652215885552143773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8546996405909028139050061 3205123652215885552143773)
                      ·
                        rfl

theorem cell23_6241956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_6241956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241956 prefixEnd_6241956 := by exact prefixLift 6241956
  have htrace : WordTrace (prefixWord ++ tailWord_6241956) baseStart_6241956 baseEnd_6241956 := by
    simpa [prefixWord, tailWord_6241956, baseEnd_6241956] using wordTrace_append hprefix tailTrace_6241956
  have hstable : (prefixWord ++ tailWord_6241956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241956).length < 2 ^ (prefixWord ++ tailWord_6241956).sum := by decide
  have hdescent : baseEnd_6241956 < baseStart_6241956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6241980 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_6241980 : Nat := 118140960795 + 6241980 * 2 ^ 59
def prefixEnd_6241980 : Nat := 4983230072969 + 3 ^ 40 * 6241980 * 2
def baseEnd_6241980 : Nat := 1068378658583864486081221

theorem tailTrace_6241980 : CollatzResearch.WordTrace tailWord_6241980 prefixEnd_6241980 1068378658583864486081221 := by
  unfold tailWord_6241980
  simp only [CollatzResearch.WordTrace]
  refine ⟨113831856963189990078453697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151775809284253320104604929 113831856963189990078453697)
  ·
    refine ⟨85373892722392492558840273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113831856963189990078453697 85373892722392492558840273)
    ·
      refine ⟨64030419541794369419130205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85373892722392492558840273 64030419541794369419130205)
      ·
        refine ⟨24011407328172888532173827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64030419541794369419130205 24011407328172888532173827)
        ·
          refine ⟨36017110992259332798260741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24011407328172888532173827 36017110992259332798260741)
          ·
            refine ⟨6753208311048624899673889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36017110992259332798260741 6753208311048624899673889)
            ·
              refine ⟨5064906233286468674755417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753208311048624899673889 5064906233286468674755417)
              ·
                refine ⟨3798679674964851506066563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064906233286468674755417 3798679674964851506066563)
                ·
                  refine ⟨5698019512447277259099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798679674964851506066563 5698019512447277259099845)
                  ·
                    refine ⟨1068378658583864486081221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698019512447277259099845 1068378658583864486081221)
                    ·
                      rfl

theorem cell23_6241980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_6241980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6241980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6241980 prefixEnd_6241980 := by exact prefixLift 6241980
  have htrace : WordTrace (prefixWord ++ tailWord_6241980) baseStart_6241980 baseEnd_6241980 := by
    simpa [prefixWord, tailWord_6241980, baseEnd_6241980] using wordTrace_append hprefix tailTrace_6241980
  have hstable : (prefixWord ++ tailWord_6241980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6241980).length < 2 ^ (prefixWord ++ tailWord_6241980).sum := by decide
  have hdescent : baseEnd_6241980 < baseStart_6241980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6241980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242009 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_6242009 : Nat := 118140960795 + 6242009 * 2 ^ 59
def prefixEnd_6242009 : Nat := 4983230072969 + 3 ^ 40 * 6242009 * 2
def baseEnd_6242009 : Nat := 3205150866690573844781029

theorem tailTrace_6242009 : CollatzResearch.WordTrace tailWord_6242009 prefixEnd_6242009 3205150866690573844781029 := by
  unfold tailWord_6242009
  simp only [CollatzResearch.WordTrace]
  refine ⟨227664771643274918109713081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151776514428849945406475387 227664771643274918109713081)
  ·
    refine ⟨170748578732456188582284811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227664771643274918109713081 170748578732456188582284811)
    ·
      refine ⟨256122868098684282873427217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170748578732456188582284811 256122868098684282873427217)
      ·
        refine ⟨192092151074013212155070413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256122868098684282873427217 192092151074013212155070413)
        ·
          refine ⟨72034556652754954558151405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192092151074013212155070413 72034556652754954558151405)
          ·
            refine ⟨27012958744783107959306777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72034556652754954558151405 27012958744783107959306777)
            ·
              refine ⟨20259719058587330969480083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27012958744783107959306777 20259719058587330969480083)
              ·
                refine ⟨30389578587880996454220125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20259719058587330969480083 30389578587880996454220125)
                ·
                  refine ⟨11396091970455373670332547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30389578587880996454220125 11396091970455373670332547)
                  ·
                    refine ⟨17094137955683060505498821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11396091970455373670332547 17094137955683060505498821)
                    ·
                      refine ⟨3205150866690573844781029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17094137955683060505498821 3205150866690573844781029)
                      ·
                        rfl

theorem cell23_6242009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_6242009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242009 prefixEnd_6242009 := by exact prefixLift 6242009
  have htrace : WordTrace (prefixWord ++ tailWord_6242009) baseStart_6242009 baseEnd_6242009 := by
    simpa [prefixWord, tailWord_6242009, baseEnd_6242009] using wordTrace_append hprefix tailTrace_6242009
  have hstable : (prefixWord ++ tailWord_6242009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242009).length < 2 ^ (prefixWord ++ tailWord_6242009).sum := by decide
  have hdescent : baseEnd_6242009 < baseStart_6242009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242023 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 1, 5]
def baseStart_6242023 : Nat := 118140960795 + 6242023 * 2 ^ 59
def prefixEnd_6242023 : Nat := 4983230072969 + 3 ^ 40 * 6242023 * 2
def baseEnd_6242023 : Nat := 1068386018473245596668655

theorem tailTrace_6242023 : CollatzResearch.WordTrace tailWord_6242023 prefixEnd_6242023 1068386018473245596668655 := by
  unfold tailWord_6242023
  simp only [CollatzResearch.WordTrace]
  refine ⟨227665282265224198500722723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151776854843482799000481815 227665282265224198500722723)
  ·
    refine ⟨341497923397836297751084085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227665282265224198500722723 341497923397836297751084085)
    ·
      refine ⟨32015430318547152914164133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341497923397836297751084085 32015430318547152914164133)
      ·
        refine ⟨6002893184727591171405775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32015430318547152914164133 6002893184727591171405775)
        ·
          refine ⟨9004339777091386757108663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002893184727591171405775 9004339777091386757108663)
          ·
            refine ⟨13506509665637080135662995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9004339777091386757108663 13506509665637080135662995)
            ·
              refine ⟨20259764498455620203494493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506509665637080135662995 20259764498455620203494493)
              ·
                refine ⟨7597411686920857576310435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20259764498455620203494493 7597411686920857576310435)
                ·
                  refine ⟨11396117530381286364465653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597411686920857576310435 11396117530381286364465653)
                  ·
                    refine ⟨1068386018473245596668655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11396117530381286364465653 1068386018473245596668655)
                    ·
                      rfl

theorem cell23_6242023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_6242023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242023 prefixEnd_6242023 := by exact prefixLift 6242023
  have htrace : WordTrace (prefixWord ++ tailWord_6242023) baseStart_6242023 baseEnd_6242023 := by
    simpa [prefixWord, tailWord_6242023, baseEnd_6242023] using wordTrace_append hprefix tailTrace_6242023
  have hstable : (prefixWord ++ tailWord_6242023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242023).length < 2 ^ (prefixWord ++ tailWord_6242023).sum := by decide
  have hdescent : baseEnd_6242023 < baseStart_6242023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_6242042 : Nat := 118140960795 + 6242042 * 2 ^ 59
def prefixEnd_6242042 : Nat := 4983230072969 + 3 ^ 40 * 6242042 * 2
def baseEnd_6242042 : Nat := 3205167811552172215668377

theorem tailTrace_6242042 : CollatzResearch.WordTrace tailWord_6242042 prefixEnd_6242042 3205167811552172215668377 := by
  unfold tailWord_6242042
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916493813038841186416095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151777316834770243163776253 56916493813038841186416095)
  ·
    refine ⟨85374740719558261779624143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56916493813038841186416095 85374740719558261779624143)
    ·
      refine ⟨128062111079337392669436215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85374740719558261779624143 128062111079337392669436215)
      ·
        refine ⟨192093166619006089004154323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128062111079337392669436215 192093166619006089004154323)
        ·
          refine ⟨288139749928509133506231485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192093166619006089004154323 288139749928509133506231485)
          ·
            refine ⟨108052406223190925064836807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288139749928509133506231485 108052406223190925064836807)
            ·
              refine ⟨162078609334786387597255211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108052406223190925064836807 162078609334786387597255211)
              ·
                refine ⟨243117914002179581395882817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162078609334786387597255211 243117914002179581395882817)
                ·
                  refine ⟨182338435501634686046912113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243117914002179581395882817 182338435501634686046912113)
                  ·
                    refine ⟨136753826626226014535184085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182338435501634686046912113 136753826626226014535184085)
                    ·
                      refine ⟨3205167811552172215668377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136753826626226014535184085 3205167811552172215668377)
                      ·
                        rfl

theorem cell23_6242042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_6242042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242042 prefixEnd_6242042 := by exact prefixLift 6242042
  have htrace : WordTrace (prefixWord ++ tailWord_6242042) baseStart_6242042 baseEnd_6242042 := by
    simpa [prefixWord, tailWord_6242042, baseEnd_6242042] using wordTrace_append hprefix tailTrace_6242042
  have hstable : (prefixWord ++ tailWord_6242042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242042).length < 2 ^ (prefixWord ++ tailWord_6242042).sum := by decide
  have hdescent : baseEnd_6242042 < baseStart_6242042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242066 : List Nat := [3, 2, 4, 1, 1, 2, 1, 9]
def baseStart_6242066 : Nat := 118140960795 + 6242066 * 2 ^ 59
def prefixEnd_6242066 : Nat := 4983230072969 + 3 ^ 40 * 6242066 * 2
def baseEnd_6242066 : Nat := 118710375373625189695121

theorem tailTrace_6242066 : CollatzResearch.WordTrace tailWord_6242066 prefixEnd_6242066 118710375373625189695121 := by
  unfold tailWord_6242066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916712651017104211134513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151777900402712277896358701 56916712651017104211134513)
  ·
    refine ⟨42687534488262828158350885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56916712651017104211134513 42687534488262828158350885)
    ·
      refine ⟨8003912716549280279690791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42687534488262828158350885 8003912716549280279690791)
      ·
        refine ⟨12005869074823920419536187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003912716549280279690791 12005869074823920419536187)
        ·
          refine ⟨18008803612235880629304281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005869074823920419536187 18008803612235880629304281)
          ·
            refine ⟨13506602709176910471978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18008803612235880629304281 13506602709176910471978211)
            ·
              refine ⟨20259904063765365707967317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506602709176910471978211 20259904063765365707967317)
              ·
                refine ⟨118710375373625189695121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20259904063765365707967317 118710375373625189695121)
                ·
                  rfl

theorem cell23_6242066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_6242066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242066 prefixEnd_6242066 := by exact prefixLift 6242066
  have htrace : WordTrace (prefixWord ++ tailWord_6242066) baseStart_6242066 baseEnd_6242066 := by
    simpa [prefixWord, tailWord_6242066, baseEnd_6242066] using wordTrace_append hprefix tailTrace_6242066
  have hstable : (prefixWord ++ tailWord_6242066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242066).length < 2 ^ (prefixWord ++ tailWord_6242066).sum := by decide
  have hdescent : baseEnd_6242066 < baseStart_6242066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242076 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6242076 : Nat := 118140960795 + 6242076 * 2 ^ 59
def prefixEnd_6242076 : Nat := 4983230072969 + 3 ^ 40 * 6242076 * 2
def baseEnd_6242076 : Nat := 3205185269894425082643221

theorem tailTrace_6242076 : CollatzResearch.WordTrace tailWord_6242076 prefixEnd_6242076 3205185269894425082643221 := by
  unfold tailWord_6242076
  simp only [CollatzResearch.WordTrace]
  refine ⟨113833607667016094276201041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151778143556021459034934721 113833607667016094276201041)
  ·
    refine ⟨85375205750262070707150781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113833607667016094276201041 85375205750262070707150781)
    ·
      refine ⟨32015702156348276515181543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85375205750262070707150781 32015702156348276515181543)
      ·
        refine ⟨48023553234522414772772315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32015702156348276515181543 48023553234522414772772315)
        ·
          refine ⟨72035329851783622159158473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48023553234522414772772315 72035329851783622159158473)
          ·
            refine ⟨54026497388837716619368855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72035329851783622159158473 54026497388837716619368855)
            ·
              refine ⟨81039746083256574929053283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54026497388837716619368855 81039746083256574929053283)
              ·
                refine ⟨121559619124884862393579925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81039746083256574929053283 121559619124884862393579925)
                ·
                  refine ⟨5698107146478977924699059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121559619124884862393579925 5698107146478977924699059)
                  ·
                    refine ⟨8547160719718466887048589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698107146478977924699059 8547160719718466887048589)
                    ·
                      refine ⟨3205185269894425082643221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547160719718466887048589 3205185269894425082643221)
                      ·
                        rfl

theorem cell23_6242076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6242076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242076 prefixEnd_6242076 := by exact prefixLift 6242076
  have htrace : WordTrace (prefixWord ++ tailWord_6242076) baseStart_6242076 baseEnd_6242076 := by
    simpa [prefixWord, tailWord_6242076, baseEnd_6242076] using wordTrace_append hprefix tailTrace_6242076
  have hstable : (prefixWord ++ tailWord_6242076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242076).length < 2 ^ (prefixWord ++ tailWord_6242076).sum := by decide
  have hdescent : baseEnd_6242076 < baseStart_6242076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242094 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6242094 : Nat := 118140960795 + 6242094 * 2 ^ 59
def prefixEnd_6242094 : Nat := 4983230072969 + 3 ^ 40 * 6242094 * 2
def baseEnd_6242094 : Nat := 3205194512546206012218139

theorem tailTrace_6242094 : CollatzResearch.WordTrace tailWord_6242094 prefixEnd_6242094 3205194512546206012218139 := by
  unfold tailWord_6242094
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458483980995872203319667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151778581231977985084371557 28458483980995872203319667)
  ·
    refine ⟨42687725971493808304979501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28458483980995872203319667 42687725971493808304979501)
    ·
      refine ⟨16007897239310178114367313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42687725971493808304979501 16007897239310178114367313)
      ·
        refine ⟨12005922929482633585775485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16007897239310178114367313 12005922929482633585775485)
        ·
          refine ⟨4502221098555987594665807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12005922929482633585775485 4502221098555987594665807)
          ·
            refine ⟨6753331647833981391998711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502221098555987594665807 6753331647833981391998711)
            ·
              refine ⟨10129997471750972087998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753331647833981391998711 10129997471750972087998067)
              ·
                refine ⟨15194996207626458131997101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129997471750972087998067 15194996207626458131997101)
                ·
                  refine ⟨5698123577859921799498913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15194996207626458131997101 5698123577859921799498913)
                  ·
                    refine ⟨4273592683394941349624185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5698123577859921799498913 4273592683394941349624185)
                    ·
                      refine ⟨3205194512546206012218139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273592683394941349624185 3205194512546206012218139)
                      ·
                        rfl

theorem cell23_6242094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6242094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242094 prefixEnd_6242094 := by exact prefixLift 6242094
  have htrace : WordTrace (prefixWord ++ tailWord_6242094) baseStart_6242094 baseEnd_6242094 := by
    simpa [prefixWord, tailWord_6242094, baseEnd_6242094] using wordTrace_append hprefix tailTrace_6242094
  have hstable : (prefixWord ++ tailWord_6242094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242094).length < 2 ^ (prefixWord ++ tailWord_6242094).sum := by decide
  have hdescent : baseEnd_6242094 < baseStart_6242094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242110 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_6242110 : Nat := 118140960795 + 6242110 * 2 ^ 59
def prefixEnd_6242110 : Nat := 4983230072969 + 3 ^ 40 * 6242110 * 2
def baseEnd_6242110 : Nat := 3205202728236677949618065

theorem tailTrace_6242110 : CollatzResearch.WordTrace tailWord_6242110 prefixEnd_6242110 3205202728236677949618065 := by
  unfold tailWord_6242110
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458556926988626544892473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151778970277272674906093189 28458556926988626544892473)
  ·
    refine ⟨21343917695241469908669355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28458556926988626544892473 21343917695241469908669355)
    ·
      refine ⟨32015876542862204863004033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21343917695241469908669355 32015876542862204863004033)
      ·
        refine ⟨24011907407146653647253025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32015876542862204863004033 24011907407146653647253025)
        ·
          refine ⟨18008930555359990235439769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24011907407146653647253025 18008930555359990235439769)
          ·
            refine ⟨13506697916519992676579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18008930555359990235439769 13506697916519992676579827)
            ·
              refine ⟨20260046874779989014869741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506697916519992676579827 20260046874779989014869741)
              ·
                refine ⟨7597517578042495880576153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20260046874779989014869741 7597517578042495880576153)
                ·
                  refine ⟨5698138183531871910432115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7597517578042495880576153 5698138183531871910432115)
                  ·
                    refine ⟨8547207275297807865648173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698138183531871910432115 8547207275297807865648173)
                    ·
                      refine ⟨3205202728236677949618065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547207275297807865648173 3205202728236677949618065)
                      ·
                        rfl

theorem cell23_6242110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_6242110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242110 prefixEnd_6242110 := by exact prefixLift 6242110
  have htrace : WordTrace (prefixWord ++ tailWord_6242110) baseStart_6242110 baseEnd_6242110 := by
    simpa [prefixWord, tailWord_6242110, baseEnd_6242110] using wordTrace_append hprefix tailTrace_6242110
  have hstable : (prefixWord ++ tailWord_6242110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242110).length < 2 ^ (prefixWord ++ tailWord_6242110).sum := by decide
  have hdescent : baseEnd_6242110 < baseStart_6242110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242119 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_6242119 : Nat := 118140960795 + 6242119 * 2 ^ 59
def prefixEnd_6242119 : Nat := 4983230072969 + 3 ^ 40 * 6242119 * 2
def baseEnd_6242119 : Nat := 3205207349562568414405523

theorem tailTrace_6242119 : CollatzResearch.WordTrace tailWord_6242119 prefixEnd_6242119 3205207349562568414405523 := by
  unfold tailWord_6242119
  simp only [CollatzResearch.WordTrace]
  refine ⟨227668783672876406896217411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151779189115250937930811607 227668783672876406896217411)
  ·
    refine ⟨341503175509314610344326117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227668783672876406896217411 341503175509314610344326117)
    ·
      refine ⟨64031845407996489439561147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341503175509314610344326117 64031845407996489439561147)
      ·
        refine ⟨96047768111994734159341721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64031845407996489439561147 96047768111994734159341721)
        ·
          refine ⟨72035826083996050619506291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96047768111994734159341721 72035826083996050619506291)
          ·
            refine ⟨108053739125994075929259437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72035826083996050619506291 108053739125994075929259437)
            ·
              refine ⟨40520152172247778473472289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108053739125994075929259437 40520152172247778473472289)
              ·
                refine ⟨30390114129185833855104217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40520152172247778473472289 30390114129185833855104217)
                ·
                  refine ⟨22792585596889375391328163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30390114129185833855104217 22792585596889375391328163)
                  ·
                    refine ⟨34188878395334063086992245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22792585596889375391328163 34188878395334063086992245)
                    ·
                      refine ⟨3205207349562568414405523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34188878395334063086992245 3205207349562568414405523)
                      ·
                        rfl

theorem cell23_6242119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_6242119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242119 prefixEnd_6242119 := by exact prefixLift 6242119
  have htrace : WordTrace (prefixWord ++ tailWord_6242119) baseStart_6242119 baseEnd_6242119 := by
    simpa [prefixWord, tailWord_6242119, baseEnd_6242119] using wordTrace_append hprefix tailTrace_6242119
  have hstable : (prefixWord ++ tailWord_6242119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242119).length < 2 ^ (prefixWord ++ tailWord_6242119).sum := by decide
  have hdescent : baseEnd_6242119 < baseStart_6242119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242120 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_6242120 : Nat := 118140960795 + 6242120 * 2 ^ 59
def prefixEnd_6242120 : Nat := 4983230072969 + 3 ^ 40 * 6242120 * 2
def baseEnd_6242120 : Nat := 3205207863043222910493019

theorem tailTrace_6242120 : CollatzResearch.WordTrace tailWord_6242120 prefixEnd_6242120 3205207863043222910493019 := by
  unfold tailWord_6242120
  simp only [CollatzResearch.WordTrace]
  refine ⟨113834410072936392033501907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151779213430581856044669209 113834410072936392033501907)
  ·
    refine ⟨170751615109404588050252861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113834410072936392033501907 170751615109404588050252861)
    ·
      refine ⟨64031855666026720518844823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170751615109404588050252861 64031855666026720518844823)
      ·
        refine ⟨96047783499040080778267235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64031855666026720518844823 96047783499040080778267235)
        ·
          refine ⟨144071675248560121167400853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96047783499040080778267235 144071675248560121167400853)
          ·
            refine ⟨6753359777276255679721915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144071675248560121167400853 6753359777276255679721915)
            ·
              refine ⟨10130039665914383519582873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753359777276255679721915 10130039665914383519582873)
              ·
                refine ⟨7597529749435787639687155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10130039665914383519582873 7597529749435787639687155)
                ·
                  refine ⟨11396294624153681459530733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597529749435787639687155 11396294624153681459530733)
                  ·
                    refine ⟨4273610484057630547324025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11396294624153681459530733 4273610484057630547324025)
                    ·
                      refine ⟨3205207863043222910493019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273610484057630547324025 3205207863043222910493019)
                      ·
                        rfl

theorem cell23_6242120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_6242120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242120 prefixEnd_6242120 := by exact prefixLift 6242120
  have htrace : WordTrace (prefixWord ++ tailWord_6242120) baseStart_6242120 baseEnd_6242120 := by
    simpa [prefixWord, tailWord_6242120, baseEnd_6242120] using wordTrace_append hprefix tailTrace_6242120
  have hstable : (prefixWord ++ tailWord_6242120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242120).length < 2 ^ (prefixWord ++ tailWord_6242120).sum := by decide
  have hdescent : baseEnd_6242120 < baseStart_6242120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242133 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6242133 : Nat := 118140960795 + 6242133 * 2 ^ 59
def prefixEnd_6242133 : Nat := 4983230072969 + 3 ^ 40 * 6242133 * 2
def baseEnd_6242133 : Nat := 3205214538291731359630459

theorem tailTrace_6242133 : CollatzResearch.WordTrace tailWord_6242133 prefixEnd_6242133 3205214538291731359630459 := by
  unfold tailWord_6242133
  simp only [CollatzResearch.WordTrace]
  refine ⟨227669294294825687287227053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151779529529883791524818035 227669294294825687287227053)
  ·
    refine ⟨85375985360559632732710145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227669294294825687287227053 85375985360559632732710145)
    ·
      refine ⟨64031989020419724549532609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85375985360559632732710145 64031989020419724549532609)
      ·
        refine ⟨48023991765314793412149457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64031989020419724549532609 48023991765314793412149457)
        ·
          refine ⟨36017993823986095059112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48023991765314793412149457 36017993823986095059112093)
          ·
            refine ⟨13506747683994785647167035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36017993823986095059112093 13506747683994785647167035)
            ·
              refine ⟨20260121525992178470750553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506747683994785647167035 20260121525992178470750553)
              ·
                refine ⟨15195091144494133853062915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20260121525992178470750553 15195091144494133853062915)
                ·
                  refine ⟨22792636716741200779594373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15195091144494133853062915 22792636716741200779594373)
                  ·
                    refine ⟨4273619384388975146173945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22792636716741200779594373 4273619384388975146173945)
                    ·
                      refine ⟨3205214538291731359630459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273619384388975146173945 3205214538291731359630459)
                      ·
                        rfl

theorem cell23_6242133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6242133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242133 prefixEnd_6242133 := by exact prefixLift 6242133
  have htrace : WordTrace (prefixWord ++ tailWord_6242133) baseStart_6242133 baseEnd_6242133 := by
    simpa [prefixWord, tailWord_6242133, baseEnd_6242133] using wordTrace_append hprefix tailTrace_6242133
  have hstable : (prefixWord ++ tailWord_6242133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242133).length < 2 ^ (prefixWord ++ tailWord_6242133).sum := by decide
  have hdescent : baseEnd_6242133 < baseStart_6242133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242169 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_6242169 : Nat := 118140960795 + 6242169 * 2 ^ 59
def prefixEnd_6242169 : Nat := 4983230072969 + 3 ^ 40 * 6242169 * 2
def baseEnd_6242169 : Nat := 1068411007865097739593431

theorem tailTrace_6242169 : CollatzResearch.WordTrace tailWord_6242169 prefixEnd_6242169 1068411007865097739593431 := by
  unfold tailWord_6242169
  simp only [CollatzResearch.WordTrace]
  refine ⟨227670607322695265435537561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151780404881796843623691707 227670607322695265435537561)
  ·
    refine ⟨170752955492021449076653171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227670607322695265435537561 170752955492021449076653171)
    ·
      refine ⟨256129433238032173614979757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170752955492021449076653171 256129433238032173614979757)
      ·
        refine ⟨96048537464262065105617409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256129433238032173614979757 96048537464262065105617409)
        ·
          refine ⟨72036403098196548829213057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96048537464262065105617409 72036403098196548829213057)
          ·
            refine ⟨54027302323647411621909793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72036403098196548829213057 54027302323647411621909793)
            ·
              refine ⟨40520476742735558716432345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54027302323647411621909793 40520476742735558716432345)
              ·
                refine ⟨30390357557051669037324259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40520476742735558716432345 30390357557051669037324259)
                ·
                  refine ⟨45585536335577503555986389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30390357557051669037324259 45585536335577503555986389)
                  ·
                    refine ⟨1068411007865097739593431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45585536335577503555986389 1068411007865097739593431)
                    ·
                      rfl

theorem cell23_6242169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_6242169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242169 prefixEnd_6242169 := by exact prefixLift 6242169
  have htrace : WordTrace (prefixWord ++ tailWord_6242169) baseStart_6242169 baseEnd_6242169 := by
    simpa [prefixWord, tailWord_6242169, baseEnd_6242169] using wordTrace_append hprefix tailTrace_6242169
  have hstable : (prefixWord ++ tailWord_6242169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242169).length < 2 ^ (prefixWord ++ tailWord_6242169).sum := by decide
  have hdescent : baseEnd_6242169 < baseStart_6242169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242176 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2]
def baseStart_6242176 : Nat := 118140960795 + 6242176 * 2 ^ 59
def prefixEnd_6242176 : Nat := 4983230072969 + 3 ^ 40 * 6242176 * 2
def baseEnd_6242176 : Nat := 3205236617959874691392761

theorem tailTrace_6242176 : CollatzResearch.WordTrace tailWord_6242176 prefixEnd_6242176 3205236617959874691392761 := by
  unfold tailWord_6242176
  simp only [CollatzResearch.WordTrace]
  refine ⟨113835431316834952815521191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151780575089113270420694921 113835431316834952815521191)
  ·
    refine ⟨170753146975252429223281787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113835431316834952815521191 170753146975252429223281787)
    ·
      refine ⟨256129720462878643834922681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170753146975252429223281787 256129720462878643834922681)
      ·
        refine ⟨192097290347158982876192011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256129720462878643834922681 192097290347158982876192011)
        ·
          refine ⟨288145935520738474314288017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192097290347158982876192011 288145935520738474314288017)
          ·
            refine ⟨216109451640553855735716013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288145935520738474314288017 216109451640553855735716013)
            ·
              refine ⟨81041044365207695900893505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216109451640553855735716013 81041044365207695900893505)
              ·
                refine ⟨60780783273905771925670129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81041044365207695900893505 60780783273905771925670129)
                ·
                  refine ⟨45585587455429328944252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60780783273905771925670129 45585587455429328944252597)
                  ·
                    refine ⟨4273648823946499588523681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45585587455429328944252597 4273648823946499588523681)
                    ·
                      refine ⟨3205236617959874691392761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273648823946499588523681 3205236617959874691392761)
                      ·
                        rfl

theorem cell23_6242176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_6242176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242176 prefixEnd_6242176 := by exact prefixLift 6242176
  have htrace : WordTrace (prefixWord ++ tailWord_6242176) baseStart_6242176 baseEnd_6242176 := by
    simpa [prefixWord, tailWord_6242176, baseEnd_6242176] using wordTrace_append hprefix tailTrace_6242176
  have hstable : (prefixWord ++ tailWord_6242176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242176).length < 2 ^ (prefixWord ++ tailWord_6242176).sum := by decide
  have hdescent : baseEnd_6242176 < baseStart_6242176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_6242219 : Nat := 118140960795 + 6242219 * 2 ^ 59
def prefixEnd_6242219 : Nat := 4983230072969 + 3 ^ 40 * 6242219 * 2
def baseEnd_6242219 : Nat := 3205258697628018023155063

theorem tailTrace_6242219 : CollatzResearch.WordTrace tailWord_6242219 prefixEnd_6242219 3205258697628018023155063 := by
  unfold tailWord_6242219
  simp only [CollatzResearch.WordTrace]
  refine ⟨227672430972514123974857711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151781620648342749316571807 227672430972514123974857711)
  ·
    refine ⟨341508646458771185962286567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227672430972514123974857711 341508646458771185962286567)
    ·
      refine ⟨512262969688156778943429851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341508646458771185962286567 512262969688156778943429851)
      ·
        refine ⟨768394454532235168415144777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512262969688156778943429851 768394454532235168415144777)
        ·
          refine ⟨576295840899176376311358583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768394454532235168415144777 576295840899176376311358583)
          ·
            refine ⟨864443761348764564467037875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576295840899176376311358583 864443761348764564467037875)
            ·
              refine ⟨1296665642023146846700556813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864443761348764564467037875 1296665642023146846700556813)
              ·
                refine ⟨486249615758680067512708805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296665642023146846700556813 486249615758680067512708805)
                ·
                  refine ⟨91171802954752512658632901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486249615758680067512708805 91171802954752512658632901)
                  ·
                    refine ⟨17094713054016096123493669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91171802954752512658632901 17094713054016096123493669)
                    ·
                      refine ⟨3205258697628018023155063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17094713054016096123493669 3205258697628018023155063)
                      ·
                        rfl

theorem cell23_6242219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_6242219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242219 prefixEnd_6242219 := by exact prefixLift 6242219
  have htrace : WordTrace (prefixWord ++ tailWord_6242219) baseStart_6242219 baseEnd_6242219 := by
    simpa [prefixWord, tailWord_6242219, baseEnd_6242219] using wordTrace_append hprefix tailTrace_6242219
  have hstable : (prefixWord ++ tailWord_6242219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242219).length < 2 ^ (prefixWord ++ tailWord_6242219).sum := by decide
  have hdescent : baseEnd_6242219 < baseStart_6242219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242249 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_6242249 : Nat := 118140960795 + 6242249 * 2 ^ 59
def prefixEnd_6242249 : Nat := 4983230072969 + 3 ^ 40 * 6242249 * 2
def baseEnd_6242249 : Nat := 3205274102047652905779925

theorem tailTrace_6242249 : CollatzResearch.WordTrace tailWord_6242249 prefixEnd_6242249 3205274102047652905779925 := by
  unfold tailWord_6242249
  simp only [CollatzResearch.WordTrace]
  refine ⟨227673525162405439098449801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151782350108270292732299867 227673525162405439098449801)
  ·
    refine ⟨170755143871804079323837351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227673525162405439098449801 170755143871804079323837351)
    ·
      refine ⟨256132715807706118985756027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170755143871804079323837351 256132715807706118985756027)
      ·
        refine ⟨384199073711559178478634041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256132715807706118985756027 384199073711559178478634041)
        ·
          refine ⟨288149305283669383858975531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384199073711559178478634041 288149305283669383858975531)
          ·
            refine ⟨432223957925504075788463297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288149305283669383858975531 432223957925504075788463297)
            ·
              refine ⟨324167968444128056841347473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432223957925504075788463297 324167968444128056841347473)
              ·
                refine ⟨243125976333096042631010605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324167968444128056841347473 243125976333096042631010605)
                ·
                  refine ⟨91172241124911015986628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243125976333096042631010605 91172241124911015986628977)
                  ·
                    refine ⟨68379180843683261989971733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91172241124911015986628977 68379180843683261989971733)
                    ·
                      refine ⟨3205274102047652905779925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68379180843683261989971733 3205274102047652905779925)
                      ·
                        rfl

theorem cell23_6242249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_6242249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242249 prefixEnd_6242249 := by exact prefixLift 6242249
  have htrace : WordTrace (prefixWord ++ tailWord_6242249) baseStart_6242249 baseEnd_6242249 := by
    simpa [prefixWord, tailWord_6242249, baseEnd_6242249] using wordTrace_append hprefix tailTrace_6242249
  have hstable : (prefixWord ++ tailWord_6242249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242249).length < 2 ^ (prefixWord ++ tailWord_6242249).sum := by decide
  have hdescent : baseEnd_6242249 < baseStart_6242249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242250 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_6242250 : Nat := 118140960795 + 6242250 * 2 ^ 59
def prefixEnd_6242250 : Nat := 4983230072969 + 3 ^ 40 * 6242250 * 2
def baseEnd_6242250 : Nat := 1068424871842769133955807

theorem tailTrace_6242250 : CollatzResearch.WordTrace tailWord_6242250 prefixEnd_6242250 1068424871842769133955807 := by
  unfold tailWord_6242250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56918390408850454067309051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151782374423601210846157469 56918390408850454067309051)
  ·
    refine ⟨85377585613275681100963577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56918390408850454067309051 85377585613275681100963577)
    ·
      refine ⟨64033189209956760825722683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85377585613275681100963577 64033189209956760825722683)
      ·
        refine ⟨96049783814935141238584025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64033189209956760825722683 96049783814935141238584025)
        ·
          refine ⟨72037337861201355928938019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96049783814935141238584025 72037337861201355928938019)
          ·
            refine ⟨108056006791802033893407029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72037337861201355928938019 108056006791802033893407029)
            ·
              refine ⟨10130250636731440677506909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108056006791802033893407029 10130250636731440677506909)
              ·
                refine ⟨3798843988774290254065091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10130250636731440677506909 3798843988774290254065091)
                ·
                  refine ⟨5698265983161435381097637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798843988774290254065091 5698265983161435381097637)
                  ·
                    refine ⟨1068424871842769133955807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698265983161435381097637 1068424871842769133955807)
                    ·
                      rfl

theorem cell23_6242250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_6242250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242250 prefixEnd_6242250 := by exact prefixLift 6242250
  have htrace : WordTrace (prefixWord ++ tailWord_6242250) baseStart_6242250 baseEnd_6242250 := by
    simpa [prefixWord, tailWord_6242250, baseEnd_6242250] using wordTrace_append hprefix tailTrace_6242250
  have hstable : (prefixWord ++ tailWord_6242250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242250).length < 2 ^ (prefixWord ++ tailWord_6242250).sum := by decide
  have hdescent : baseEnd_6242250 < baseStart_6242250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242276 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_6242276 : Nat := 118140960795 + 6242276 * 2 ^ 59
def prefixEnd_6242276 : Nat := 4983230072969 + 3 ^ 40 * 6242276 * 2
def baseEnd_6242276 : Nat := 1068429322008441433380767

theorem tailTrace_6242276 : CollatzResearch.WordTrace tailWord_6242276 prefixEnd_6242276 1068429322008441433380767 := by
  unfold tailWord_6242276
  simp only [CollatzResearch.WordTrace]
  refine ⟨113837254966653811354841341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151783006622205081806455121 113837254966653811354841341)
  ·
    refine ⟨42688970612495179258065503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113837254966653811354841341 42688970612495179258065503)
    ·
      refine ⟨64033455918742768887098255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42688970612495179258065503 64033455918742768887098255)
      ·
        refine ⟨96050183878114153330647383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64033455918742768887098255 96050183878114153330647383)
        ·
          refine ⟨144075275817171229995971075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96050183878114153330647383 144075275817171229995971075)
          ·
            refine ⟨216112913725756844993956613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144075275817171229995971075 216112913725756844993956613)
            ·
              refine ⟨40521171323579408436366865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216112913725756844993956613 40521171323579408436366865)
              ·
                refine ⟨30390878492684556327275149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40521171323579408436366865 30390878492684556327275149)
                ·
                  refine ⟨11396579434756708622728181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30390878492684556327275149 11396579434756708622728181)
                  ·
                    refine ⟨1068429322008441433380767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11396579434756708622728181 1068429322008441433380767)
                    ·
                      rfl

theorem cell23_6242276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_6242276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242276 prefixEnd_6242276 := by exact prefixLift 6242276
  have htrace : WordTrace (prefixWord ++ tailWord_6242276) baseStart_6242276 baseEnd_6242276 := by
    simpa [prefixWord, tailWord_6242276, baseEnd_6242276] using wordTrace_append hprefix tailTrace_6242276
  have hstable : (prefixWord ++ tailWord_6242276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242276).length < 2 ^ (prefixWord ++ tailWord_6242276).sum := by decide
  have hdescent : baseEnd_6242276 < baseStart_6242276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242300 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_6242300 : Nat := 118140960795 + 6242300 * 2 ^ 59
def prefixEnd_6242300 : Nat := 4983230072969 + 3 ^ 40 * 6242300 * 2
def baseEnd_6242300 : Nat := 3205300289561032206242191

theorem tailTrace_6242300 : CollatzResearch.WordTrace tailWord_6242300 prefixEnd_6242300 3205300289561032206242191 := by
  unfold tailWord_6242300
  simp only [CollatzResearch.WordTrace]
  refine ⟨113837692642610337404278177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151783590190147116539037569 113837692642610337404278177)
  ·
    refine ⟨85378269481957753053208633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113837692642610337404278177 85378269481957753053208633)
    ·
      refine ⟨64033702111468314789906475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85378269481957753053208633 64033702111468314789906475)
      ·
        refine ⟨96050553167202472184859713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64033702111468314789906475 96050553167202472184859713)
        ·
          refine ⟨72037914875401854138644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96050553167202472184859713 72037914875401854138644785)
          ·
            refine ⟨54028436156551390603983589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72037914875401854138644785 54028436156551390603983589)
            ·
              refine ⟨10130331779353385738246923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54028436156551390603983589 10130331779353385738246923)
              ·
                refine ⟨15195497669030078607370385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130331779353385738246923 15195497669030078607370385)
                ·
                  refine ⟨11396623251772558955527789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15195497669030078607370385 11396623251772558955527789)
                  ·
                    refine ⟨4273733719414709608322921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11396623251772558955527789 4273733719414709608322921)
                    ·
                      refine ⟨3205300289561032206242191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273733719414709608322921 3205300289561032206242191)
                      ·
                        rfl

theorem cell23_6242300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_6242300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242300 prefixEnd_6242300 := by exact prefixLift 6242300
  have htrace : WordTrace (prefixWord ++ tailWord_6242300) baseStart_6242300 baseEnd_6242300 := by
    simpa [prefixWord, tailWord_6242300, baseEnd_6242300] using wordTrace_append hprefix tailTrace_6242300
  have hstable : (prefixWord ++ tailWord_6242300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242300).length < 2 ^ (prefixWord ++ tailWord_6242300).sum := by decide
  have hdescent : baseEnd_6242300 < baseStart_6242300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242323 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 2, 4]
def baseStart_6242323 : Nat := 118140960795 + 6242323 * 2 ^ 59
def prefixEnd_6242323 : Nat := 4983230072969 + 3 ^ 40 * 6242323 * 2
def baseEnd_6242323 : Nat := 1068437366538695205418195

theorem tailTrace_6242323 : CollatzResearch.WordTrace tailWord_6242323 prefixEnd_6242323 1068437366538695205418195 := by
  unfold tailWord_6242323
  simp only [CollatzResearch.WordTrace]
  refine ⟨227676224164137349736643623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151784149442758233157762415 227676224164137349736643623)
  ·
    refine ⟨341514336246206024604965435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227676224164137349736643623 341514336246206024604965435)
    ·
      refine ⟨512271504369309036907448153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341514336246206024604965435 512271504369309036907448153)
      ·
        refine ⟨384203628276981777680586115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512271504369309036907448153 384203628276981777680586115)
        ·
          refine ⟨576305442415472666520879173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384203628276981777680586115 576305442415472666520879173)
          ·
            refine ⟨108057270452901124972664845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576305442415472666520879173 108057270452901124972664845)
            ·
              refine ⟨40521476419837921864749317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108057270452901124972664845 40521476419837921864749317)
              ·
                refine ⟨7597776828719610349640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40521476419837921864749317 7597776828719610349640497)
                ·
                  refine ⟨5698332621539707762230373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7597776828719610349640497 5698332621539707762230373)
                  ·
                    refine ⟨1068437366538695205418195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698332621539707762230373 1068437366538695205418195)
                    ·
                      rfl

theorem cell23_6242323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 4].length) (baseStart_6242323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242323 prefixEnd_6242323 := by exact prefixLift 6242323
  have htrace : WordTrace (prefixWord ++ tailWord_6242323) baseStart_6242323 baseEnd_6242323 := by
    simpa [prefixWord, tailWord_6242323, baseEnd_6242323] using wordTrace_append hprefix tailTrace_6242323
  have hstable : (prefixWord ++ tailWord_6242323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242323).length < 2 ^ (prefixWord ++ tailWord_6242323).sum := by decide
  have hdescent : baseEnd_6242323 < baseStart_6242323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242340 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_6242340 : Nat := 118140960795 + 6242340 * 2 ^ 59
def prefixEnd_6242340 : Nat := 4983230072969 + 3 ^ 40 * 6242340 * 2
def baseEnd_6242340 : Nat := 1068440276262404016580669

theorem tailTrace_6242340 : CollatzResearch.WordTrace tailWord_6242340 prefixEnd_6242340 1068440276262404016580669 := by
  unfold tailWord_6242340
  simp only [CollatzResearch.WordTrace]
  refine ⟨113838422102537880820006237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151784562803383841093341649 113838422102537880820006237)
  ·
    refine ⟨42689408288451705307502339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113838422102537880820006237 42689408288451705307502339)
    ·
      refine ⟨64034112432677557961253509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42689408288451705307502339 64034112432677557961253509)
      ·
        refine ⟨12006396081127042117735033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64034112432677557961253509 12006396081127042117735033)
        ·
          refine ⟨9004797060845281588301275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12006396081127042117735033 9004797060845281588301275)
          ·
            refine ⟨13507195591267922382451913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9004797060845281588301275 13507195591267922382451913)
            ·
              refine ⟨10130396693450941786838935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13507195591267922382451913 10130396693450941786838935)
              ·
                refine ⟨15195595040176412680258403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130396693450941786838935 15195595040176412680258403)
                ·
                  refine ⟨22793392560264619020387605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15195595040176412680258403 22793392560264619020387605)
                  ·
                    refine ⟨1068440276262404016580669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22793392560264619020387605 1068440276262404016580669)
                    ·
                      rfl

theorem cell23_6242340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_6242340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242340 prefixEnd_6242340 := by exact prefixLift 6242340
  have htrace : WordTrace (prefixWord ++ tailWord_6242340) baseStart_6242340 baseEnd_6242340 := by
    simpa [prefixWord, tailWord_6242340, baseEnd_6242340] using wordTrace_append hprefix tailTrace_6242340
  have hstable : (prefixWord ++ tailWord_6242340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242340).length < 2 ^ (prefixWord ++ tailWord_6242340).sum := by decide
  have hdescent : baseEnd_6242340 < baseStart_6242340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242350 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6242350 : Nat := 118140960795 + 6242350 * 2 ^ 59
def prefixEnd_6242350 : Nat := 4983230072969 + 3 ^ 40 * 6242350 * 2
def baseEnd_6242350 : Nat := 3205325963593757010616961

theorem tailTrace_6242350 : CollatzResearch.WordTrace tailWord_6242350 prefixEnd_6242350 3205325963593757010616961 := by
  unfold tailWord_6242350
  simp only [CollatzResearch.WordTrace]
  refine ⟨28459651116879941668484563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151784805956693022231917669 28459651116879941668484563)
  ·
    refine ⟨42689476675319912502726845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28459651116879941668484563 42689476675319912502726845)
    ·
      refine ⟨16008553753244967188522567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42689476675319912502726845 16008553753244967188522567)
      ·
        refine ⟨24012830629867450782783851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008553753244967188522567 24012830629867450782783851)
        ·
          refine ⟨36019245944801176174175777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24012830629867450782783851 36019245944801176174175777)
          ·
            refine ⟨27014434458600882130631833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36019245944801176174175777 27014434458600882130631833)
            ·
              refine ⟨20260825843950661597973875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27014434458600882130631833 20260825843950661597973875)
              ·
                refine ⟨30391238765925992396960813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20260825843950661597973875 30391238765925992396960813)
                ·
                  refine ⟨11396714537222247148860305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30391238765925992396960813 11396714537222247148860305)
                  ·
                    refine ⟨8547535902916685361645229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11396714537222247148860305 8547535902916685361645229)
                    ·
                      refine ⟨3205325963593757010616961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547535902916685361645229 3205325963593757010616961)
                      ·
                        rfl

theorem cell23_6242350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6242350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242350 prefixEnd_6242350 := by exact prefixLift 6242350
  have htrace : WordTrace (prefixWord ++ tailWord_6242350) baseStart_6242350 baseEnd_6242350 := by
    simpa [prefixWord, tailWord_6242350, baseEnd_6242350] using wordTrace_append hprefix tailTrace_6242350
  have hstable : (prefixWord ++ tailWord_6242350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242350).length < 2 ^ (prefixWord ++ tailWord_6242350).sum := by decide
  have hdescent : baseEnd_6242350 < baseStart_6242350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242353 : List Nat := [1, 2, 2, 3, 1, 4, 3, 7]
def baseStart_6242353 : Nat := 118140960795 + 6242353 * 2 ^ 59
def prefixEnd_6242353 : Nat := 4983230072969 + 3 ^ 40 * 6242353 * 2
def baseEnd_6242353 : Nat := 118715833482804462921461

theorem tailTrace_6242353 : CollatzResearch.WordTrace tailWord_6242353 prefixEnd_6242353 118715833482804462921461 := by
  unfold tailWord_6242353
  simp only [CollatzResearch.WordTrace]
  refine ⟨227677318354028664860235713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151784878902685776573490475 227677318354028664860235713)
  ·
    refine ⟨170757988765521498645176785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227677318354028664860235713 170757988765521498645176785)
    ·
      refine ⟨128068491574141123983882589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170757988765521498645176785 128068491574141123983882589)
      ·
        refine ⟨48025684340302921493955971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128068491574141123983882589 48025684340302921493955971)
        ·
          refine ⟨72038526510454382240933957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48025684340302921493955971 72038526510454382240933957)
          ·
            refine ⟨13507223720710196670175117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72038526510454382240933957 13507223720710196670175117)
            ·
              refine ⟨5065208895266323751315669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13507223720710196670175117 5065208895266323751315669)
              ·
                refine ⟨118715833482804462921461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5065208895266323751315669 118715833482804462921461)
                ·
                  rfl

theorem cell23_6242353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 7].length) (baseStart_6242353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242353 prefixEnd_6242353 := by exact prefixLift 6242353
  have htrace : WordTrace (prefixWord ++ tailWord_6242353) baseStart_6242353 baseEnd_6242353 := by
    simpa [prefixWord, tailWord_6242353, baseEnd_6242353] using wordTrace_append hprefix tailTrace_6242353
  have hstable : (prefixWord ++ tailWord_6242353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242353).length < 2 ^ (prefixWord ++ tailWord_6242353).sum := by decide
  have hdescent : baseEnd_6242353 < baseStart_6242353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242363 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 3]
def baseStart_6242363 : Nat := 118140960795 + 6242363 * 2 ^ 59
def prefixEnd_6242363 : Nat := 4983230072969 + 3 ^ 40 * 6242363 * 2
def baseEnd_6242363 : Nat := 3205332638842265459754401

theorem tailTrace_6242363 : CollatzResearch.WordTrace tailWord_6242363 prefixEnd_6242363 3205332638842265459754401 := by
  unfold tailWord_6242363
  simp only [CollatzResearch.WordTrace]
  refine ⟨227677683083992436568099743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151785122055994957712066495 227677683083992436568099743)
  ·
    refine ⟨341516524625988654852149615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227677683083992436568099743 341516524625988654852149615)
    ·
      refine ⟨512274786938982982278224423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341516524625988654852149615 512274786938982982278224423)
      ·
        refine ⟨768412180408474473417336635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512274786938982982278224423 768412180408474473417336635)
        ·
          refine ⟨1152618270612711710126004953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768412180408474473417336635 1152618270612711710126004953)
          ·
            refine ⟨864463702959533782594503715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152618270612711710126004953 864463702959533782594503715)
            ·
              refine ⟨1296695554439300673891755573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864463702959533782594503715 1296695554439300673891755573)
              ·
                refine ⟨121565208228684438177352085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1296695554439300673891755573 121565208228684438177352085)
                ·
                  refine ⟨5698369135719583039563379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121565208228684438177352085 5698369135719583039563379)
                  ·
                    refine ⟨8547553703579374559345069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698369135719583039563379 8547553703579374559345069)
                    ·
                      refine ⟨3205332638842265459754401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547553703579374559345069 3205332638842265459754401)
                      ·
                        rfl

theorem cell23_6242363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 3].length) (baseStart_6242363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242363 prefixEnd_6242363 := by exact prefixLift 6242363
  have htrace : WordTrace (prefixWord ++ tailWord_6242363) baseStart_6242363 baseEnd_6242363 := by
    simpa [prefixWord, tailWord_6242363, baseEnd_6242363] using wordTrace_append hprefix tailTrace_6242363
  have hstable : (prefixWord ++ tailWord_6242363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242363).length < 2 ^ (prefixWord ++ tailWord_6242363).sum := by decide
  have hdescent : baseEnd_6242363 < baseStart_6242363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242364 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_6242364 : Nat := 118140960795 + 6242364 * 2 ^ 59
def prefixEnd_6242364 : Nat := 4983230072969 + 3 ^ 40 * 6242364 * 2
def baseEnd_6242364 : Nat := 3205333152322919955841897

theorem tailTrace_6242364 : CollatzResearch.WordTrace tailWord_6242364 prefixEnd_6242364 3205333152322919955841897 := by
  unfold tailWord_6242364
  simp only [CollatzResearch.WordTrace]
  refine ⟨113838859778494406869443073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151785146371325875825924097 113838859778494406869443073)
  ·
    refine ⟨85379144833870805152082305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113838859778494406869443073 85379144833870805152082305)
    ·
      refine ⟨64034358625403103864061729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85379144833870805152082305 64034358625403103864061729)
      ·
        refine ⟨48025768969052327898046297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64034358625403103864061729 48025768969052327898046297)
        ·
          refine ⟨36019326726789245923534723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48025768969052327898046297 36019326726789245923534723)
          ·
            refine ⟨54028990090183868885302085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36019326726789245923534723 54028990090183868885302085)
            ·
              refine ⟨10130435641909475415994141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54028990090183868885302085 10130435641909475415994141)
              ·
                refine ⟨3798913365716053280997803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10130435641909475415994141 3798913365716053280997803)
                ·
                  refine ⟨5698370048574079921496705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798913365716053280997803 5698370048574079921496705)
                  ·
                    refine ⟨4273777536430559941122529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5698370048574079921496705 4273777536430559941122529)
                    ·
                      refine ⟨3205333152322919955841897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273777536430559941122529 3205333152322919955841897)
                      ·
                        rfl

theorem cell23_6242364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_6242364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242364 prefixEnd_6242364 := by exact prefixLift 6242364
  have htrace : WordTrace (prefixWord ++ tailWord_6242364) baseStart_6242364 baseEnd_6242364 := by
    simpa [prefixWord, tailWord_6242364, baseEnd_6242364] using wordTrace_append hprefix tailTrace_6242364
  have hstable : (prefixWord ++ tailWord_6242364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242364).length < 2 ^ (prefixWord ++ tailWord_6242364).sum := by decide
  have hdescent : baseEnd_6242364 < baseStart_6242364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242376 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6242376 : Nat := 118140960795 + 6242376 * 2 ^ 59
def prefixEnd_6242376 : Nat := 4983230072969 + 3 ^ 40 * 6242376 * 2
def baseEnd_6242376 : Nat := 3205339314090773908891841

theorem tailTrace_6242376 : CollatzResearch.WordTrace tailWord_6242376 prefixEnd_6242376 3205339314090773908891841 := by
  unfold tailWord_6242376
  simp only [CollatzResearch.WordTrace]
  refine ⟨113839078616472669894161491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151785438155296893192215321 113839078616472669894161491)
  ·
    refine ⟨170758617924709004841242237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113839078616472669894161491 170758617924709004841242237)
    ·
      refine ⟨64034481721765876815465839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170758617924709004841242237 64034481721765876815465839)
      ·
        refine ⟨96051722582648815223198759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64034481721765876815465839 96051722582648815223198759)
        ·
          refine ⟨144077583873973222834798139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96051722582648815223198759 144077583873973222834798139)
          ·
            refine ⟨216116375810959834252197209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144077583873973222834798139 216116375810959834252197209)
            ·
              refine ⟨162087281858219875689147907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216116375810959834252197209 162087281858219875689147907)
              ·
                refine ⟨243130922787329813533721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162087281858219875689147907 243130922787329813533721861)
                ·
                  refine ⟨45587048022624340037572849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243130922787329813533721861 45587048022624340037572849)
                  ·
                    refine ⟨34190286016968255028179637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45587048022624340037572849 34190286016968255028179637)
                    ·
                      refine ⟨3205339314090773908891841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34190286016968255028179637 3205339314090773908891841)
                      ·
                        rfl

theorem cell23_6242376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6242376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242376 prefixEnd_6242376 := by exact prefixLift 6242376
  have htrace : WordTrace (prefixWord ++ tailWord_6242376) baseStart_6242376 baseEnd_6242376 := by
    simpa [prefixWord, tailWord_6242376, baseEnd_6242376] using wordTrace_append hprefix tailTrace_6242376
  have hstable : (prefixWord ++ tailWord_6242376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242376).length < 2 ^ (prefixWord ++ tailWord_6242376).sum := by decide
  have hdescent : baseEnd_6242376 < baseStart_6242376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242397 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6242397 : Nat := 118140960795 + 6242397 * 2 ^ 59
def prefixEnd_6242397 : Nat := 4983230072969 + 3 ^ 40 * 6242397 * 2
def baseEnd_6242397 : Nat := 3205350097184518326729245

theorem tailTrace_6242397 : CollatzResearch.WordTrace tailWord_6242397 prefixEnd_6242397 3205350097184518326729245 := by
  unfold tailWord_6242397
  simp only [CollatzResearch.WordTrace]
  refine ⟨227678923165869260374837445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151785948777246173583224963 227678923165869260374837445)
  ·
    refine ⟨42689798093600486320282021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227678923165869260374837445 42689798093600486320282021)
    ·
      refine ⟨8004337142550091185052879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42689798093600486320282021 8004337142550091185052879)
      ·
        refine ⟨12006505713825136777579319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8004337142550091185052879 12006505713825136777579319)
        ·
          refine ⟨18009758570737705166368979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12006505713825136777579319 18009758570737705166368979)
          ·
            refine ⟨27014637856106557749553469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18009758570737705166368979 27014637856106557749553469)
            ·
              refine ⟨10130489196039959156082551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27014637856106557749553469 10130489196039959156082551)
              ·
                refine ⟨15195733794059938734123827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10130489196039959156082551 15195733794059938734123827)
                ·
                  refine ⟨22793600691089908101185741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15195733794059938734123827 22793600691089908101185741)
                  ·
                    refine ⟨8547600259158715537944653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22793600691089908101185741 8547600259158715537944653)
                    ·
                      refine ⟨3205350097184518326729245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547600259158715537944653 3205350097184518326729245)
                      ·
                        rfl

theorem cell23_6242397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6242397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242397 prefixEnd_6242397 := by exact prefixLift 6242397
  have htrace : WordTrace (prefixWord ++ tailWord_6242397) baseStart_6242397 baseEnd_6242397 := by
    simpa [prefixWord, tailWord_6242397, baseEnd_6242397] using wordTrace_append hprefix tailTrace_6242397
  have hstable : (prefixWord ++ tailWord_6242397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242397).length < 2 ^ (prefixWord ++ tailWord_6242397).sum := by decide
  have hdescent : baseEnd_6242397 < baseStart_6242397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242407 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_6242407 : Nat := 118140960795 + 6242407 * 2 ^ 59
def prefixEnd_6242407 : Nat := 4983230072969 + 3 ^ 40 * 6242407 * 2
def baseEnd_6242407 : Nat := 3205355231991063287604199

theorem tailTrace_6242407 : CollatzResearch.WordTrace tailWord_6242407 prefixEnd_6242407 3205355231991063287604199 := by
  unfold tailWord_6242407
  simp only [CollatzResearch.WordTrace]
  refine ⟨227679287895833032082701475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151786191930555354721800983 227679287895833032082701475)
  ·
    refine ⟨341518931843749548124052213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227679287895833032082701475 341518931843749548124052213)
    ·
      refine ⟨32017399860351520136629895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341518931843749548124052213 32017399860351520136629895)
      ·
        refine ⟨48026099790527280204944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32017399860351520136629895 48026099790527280204944843)
        ·
          refine ⟨72039149685790920307417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48026099790527280204944843 72039149685790920307417265)
          ·
            refine ⟨54029362264343190230562949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72039149685790920307417265 54029362264343190230562949)
            ·
              refine ⟨10130505424564348168230553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54029362264343190230562949 10130505424564348168230553)
              ·
                refine ⟨7597879068423261126172915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10130505424564348168230553 7597879068423261126172915)
                ·
                  refine ⟨11396818602634891689259373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597879068423261126172915 11396818602634891689259373)
                  ·
                    refine ⟨4273806975988084383472265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11396818602634891689259373 4273806975988084383472265)
                    ·
                      refine ⟨3205355231991063287604199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273806975988084383472265 3205355231991063287604199)
                      ·
                        rfl

theorem cell23_6242407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_6242407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242407 prefixEnd_6242407 := by exact prefixLift 6242407
  have htrace : WordTrace (prefixWord ++ tailWord_6242407) baseStart_6242407 baseEnd_6242407 := by
    simpa [prefixWord, tailWord_6242407, baseEnd_6242407] using wordTrace_append hprefix tailTrace_6242407
  have hstable : (prefixWord ++ tailWord_6242407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242407).length < 2 ^ (prefixWord ++ tailWord_6242407).sum := by decide
  have hdescent : baseEnd_6242407 < baseStart_6242407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242423 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_6242423 : Nat := 118140960795 + 6242423 * 2 ^ 59
def prefixEnd_6242423 : Nat := 4983230072969 + 3 ^ 40 * 6242423 * 2
def baseEnd_6242423 : Nat := 3205363447681535225004125

theorem tailTrace_6242423 : CollatzResearch.WordTrace tailWord_6242423 prefixEnd_6242423 3205363447681535225004125 := by
  unfold tailWord_6242423
  simp only [CollatzResearch.WordTrace]
  refine ⟨227679871463775066815283923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151786580975850044543522615 227679871463775066815283923)
  ·
    refine ⟨341519807195662600222925885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227679871463775066815283923 341519807195662600222925885)
    ·
      refine ⟨128069927698373475083597207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341519807195662600222925885 128069927698373475083597207)
      ·
        refine ⟨192104891547560212625395811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128069927698373475083597207 192104891547560212625395811)
        ·
          refine ⟨288157337321340318938093717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192104891547560212625395811 288157337321340318938093717)
          ·
            refine ⟨13507375186937827450223143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288157337321340318938093717 13507375186937827450223143)
            ·
              refine ⟨20261062780406741175334715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507375186937827450223143 20261062780406741175334715)
              ·
                refine ⟨30391594170610111763002073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261062780406741175334715 30391594170610111763002073)
                ·
                  refine ⟨22793695627957583822251555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30391594170610111763002073 22793695627957583822251555)
                  ·
                    refine ⟨34190543441936375733377333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22793695627957583822251555 34190543441936375733377333)
                    ·
                      refine ⟨3205363447681535225004125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34190543441936375733377333 3205363447681535225004125)
                      ·
                        rfl

theorem cell23_6242423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_6242423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242423 prefixEnd_6242423 := by exact prefixLift 6242423
  have htrace : WordTrace (prefixWord ++ tailWord_6242423) baseStart_6242423 baseEnd_6242423 := by
    simpa [prefixWord, tailWord_6242423, baseEnd_6242423] using wordTrace_append hprefix tailTrace_6242423
  have hstable : (prefixWord ++ tailWord_6242423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242423).length < 2 ^ (prefixWord ++ tailWord_6242423).sum := by decide
  have hdescent : baseEnd_6242423 < baseStart_6242423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242437 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_6242437 : Nat := 118140960795 + 6242437 * 2 ^ 59
def prefixEnd_6242437 : Nat := 4983230072969 + 3 ^ 40 * 6242437 * 2
def baseEnd_6242437 : Nat := 3205370636410698170229061

theorem tailTrace_6242437 : CollatzResearch.WordTrace tailWord_6242437 prefixEnd_6242437 3205370636410698170229061 := by
  unfold tailWord_6242437
  simp only [CollatzResearch.WordTrace]
  refine ⟨227680382085724347206293565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151786921390482898137529043 227680382085724347206293565)
  ·
    refine ⟨85380143282146630202360087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227680382085724347206293565 85380143282146630202360087)
    ·
      refine ⟨128070214923219945303540131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85380143282146630202360087 128070214923219945303540131)
      ·
        refine ⟨192105322384829917955310197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128070214923219945303540131 192105322384829917955310197)
        ·
          refine ⟨18009873973577804808310331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192105322384829917955310197 18009873973577804808310331)
          ·
            refine ⟨27014810960366707212465497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18009873973577804808310331 27014810960366707212465497)
            ·
              refine ⟨20261108220275030409349123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27014810960366707212465497 20261108220275030409349123)
              ·
                refine ⟨30391662330412545614023685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261108220275030409349123 30391662330412545614023685)
                ·
                  refine ⟨5698436686952352302629441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30391662330412545614023685 5698436686952352302629441)
                  ·
                    refine ⟨4273827515214264226972081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5698436686952352302629441 4273827515214264226972081)
                    ·
                      refine ⟨3205370636410698170229061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273827515214264226972081 3205370636410698170229061)
                      ·
                        rfl

theorem cell23_6242437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_6242437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242437 prefixEnd_6242437 := by exact prefixLift 6242437
  have htrace : WordTrace (prefixWord ++ tailWord_6242437) baseStart_6242437 baseEnd_6242437 := by
    simpa [prefixWord, tailWord_6242437, baseEnd_6242437] using wordTrace_append hprefix tailTrace_6242437
  have hstable : (prefixWord ++ tailWord_6242437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242437).length < 2 ^ (prefixWord ++ tailWord_6242437).sum := by decide
  have hdescent : baseEnd_6242437 < baseStart_6242437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242453 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_6242453 : Nat := 118140960795 + 6242453 * 2 ^ 59
def prefixEnd_6242453 : Nat := 4983230072969 + 3 ^ 40 * 6242453 * 2
def baseEnd_6242453 : Nat := 3205378852101170107628987

theorem tailTrace_6242453 : CollatzResearch.WordTrace tailWord_6242453 prefixEnd_6242453 3205378852101170107628987 := by
  unfold tailWord_6242453
  simp only [CollatzResearch.WordTrace]
  refine ⟨227680965653666381938876013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151787310435777587959250675 227680965653666381938876013)
  ·
    refine ⟨85380362120124893227078505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227680965653666381938876013 85380362120124893227078505)
    ·
      refine ⟨64035271590093669920308879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85380362120124893227078505 64035271590093669920308879)
      ·
        refine ⟨96052907385140504880463319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64035271590093669920308879 96052907385140504880463319)
        ·
          refine ⟨144079361077710757320694979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96052907385140504880463319 144079361077710757320694979)
          ·
            refine ⟨216119041616566135981042469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144079361077710757320694979 216119041616566135981042469)
            ·
              refine ⟨40522320303106150496445463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216119041616566135981042469 40522320303106150496445463)
              ·
                refine ⟨60783480454659225744668195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40522320303106150496445463 60783480454659225744668195)
                ·
                  refine ⟨91175220681988838617002293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60783480454659225744668195 91175220681988838617002293)
                  ·
                    refine ⟨8547676938936453620343965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91175220681988838617002293 8547676938936453620343965)
                    ·
                      refine ⟨3205378852101170107628987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547676938936453620343965 3205378852101170107628987)
                      ·
                        rfl

theorem cell23_6242453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_6242453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242453 prefixEnd_6242453 := by exact prefixLift 6242453
  have htrace : WordTrace (prefixWord ++ tailWord_6242453) baseStart_6242453 baseEnd_6242453 := by
    simpa [prefixWord, tailWord_6242453, baseEnd_6242453] using wordTrace_append hprefix tailTrace_6242453
  have hstable : (prefixWord ++ tailWord_6242453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242453).length < 2 ^ (prefixWord ++ tailWord_6242453).sum := by decide
  have hdescent : baseEnd_6242453 < baseStart_6242453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242493 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_6242493 : Nat := 118140960795 + 6242493 * 2 ^ 59
def prefixEnd_6242493 : Nat := 4983230072969 + 3 ^ 40 * 6242493 * 2
def baseEnd_6242493 : Nat := 3205399391327349951128803

theorem tailTrace_6242493 : CollatzResearch.WordTrace tailWord_6242493 prefixEnd_6242493 3205399391327349951128803 := by
  unfold tailWord_6242493
  simp only [CollatzResearch.WordTrace]
  refine ⟨227682424573521468770332133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151788283049014312513554755 227682424573521468770332133)
  ·
    refine ⟨42690454607535275394437275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227682424573521468770332133 42690454607535275394437275)
    ·
      refine ⟨64035681911302913091655913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690454607535275394437275 64035681911302913091655913)
      ·
        refine ⟨48026761433477184818741935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64035681911302913091655913 48026761433477184818741935)
        ·
          refine ⟨72040142150215777228112903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48026761433477184818741935 72040142150215777228112903)
          ·
            refine ⟨108060213225323665842169355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72040142150215777228112903 108060213225323665842169355)
            ·
              refine ⟨162090319837985498763254033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108060213225323665842169355 162090319837985498763254033)
              ·
                refine ⟨121567739878489124072440525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162090319837985498763254033 121567739878489124072440525)
                ·
                  refine ⟨45587902454433421527165197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121567739878489124072440525 45587902454433421527165197)
                  ·
                    refine ⟨17095463420412533072686949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45587902454433421527165197 17095463420412533072686949)
                    ·
                      refine ⟨3205399391327349951128803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17095463420412533072686949 3205399391327349951128803)
                      ·
                        rfl

theorem cell23_6242493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_6242493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242493 prefixEnd_6242493 := by exact prefixLift 6242493
  have htrace : WordTrace (prefixWord ++ tailWord_6242493) baseStart_6242493 baseEnd_6242493 := by
    simpa [prefixWord, tailWord_6242493, baseEnd_6242493] using wordTrace_append hprefix tailTrace_6242493
  have hstable : (prefixWord ++ tailWord_6242493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242493).length < 2 ^ (prefixWord ++ tailWord_6242493).sum := by decide
  have hdescent : baseEnd_6242493 < baseStart_6242493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242500 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6242500 : Nat := 118140960795 + 6242500 * 2 ^ 59
def prefixEnd_6242500 : Nat := 4983230072969 + 3 ^ 40 * 6242500 * 2
def baseEnd_6242500 : Nat := 3205402985691931423741271

theorem tailTrace_6242500 : CollatzResearch.WordTrace tailWord_6242500 prefixEnd_6242500 3205402985691931423741271 := by
  unfold tailWord_6242500
  simp only [CollatzResearch.WordTrace]
  refine ⟨113841339942248054482918477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151788453256330739310557969 113841339942248054482918477)
  ·
    refine ⟨42690502478343020431094429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113841339942248054482918477 42690502478343020431094429)
    ·
      refine ⟨16008938429378632661660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42690502478343020431094429 16008938429378632661660411)
      ·
        refine ⟨24013407644067948992490617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008938429378632661660411 24013407644067948992490617)
        ·
          refine ⟨18010055733050961744367963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24013407644067948992490617 18010055733050961744367963)
          ·
            refine ⟨27015083599576442616551945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18010055733050961744367963 27015083599576442616551945)
            ·
              refine ⟨20261312699682331962413959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27015083599576442616551945 20261312699682331962413959)
              ·
                refine ⟨30391969049523497943620939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261312699682331962413959 30391969049523497943620939)
                ·
                  refine ⟨45587953574285246915431409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30391969049523497943620939 45587953574285246915431409)
                  ·
                    refine ⟨34190965180713935186573557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45587953574285246915431409 34190965180713935186573557)
                    ·
                      refine ⟨3205402985691931423741271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34190965180713935186573557 3205402985691931423741271)
                      ·
                        rfl

theorem cell23_6242500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6242500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242500 prefixEnd_6242500 := by exact prefixLift 6242500
  have htrace : WordTrace (prefixWord ++ tailWord_6242500) baseStart_6242500 baseEnd_6242500 := by
    simpa [prefixWord, tailWord_6242500, baseEnd_6242500] using wordTrace_append hprefix tailTrace_6242500
  have hstable : (prefixWord ++ tailWord_6242500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242500).length < 2 ^ (prefixWord ++ tailWord_6242500).sum := by decide
  have hdescent : baseEnd_6242500 < baseStart_6242500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242520 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_6242520 : Nat := 118140960795 + 6242520 * 2 ^ 59
def prefixEnd_6242520 : Nat := 4983230072969 + 3 ^ 40 * 6242520 * 2
def baseEnd_6242520 : Nat := 1068471085101673781830393

theorem tailTrace_6242520 : CollatzResearch.WordTrace tailWord_6242520 prefixEnd_6242520 1068471085101673781830393 := by
  unfold tailWord_6242520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113841704672211826190782507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151788939562949101587710009 113841704672211826190782507)
  ·
    refine ⟨170762557008317739286173761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113841704672211826190782507 170762557008317739286173761)
    ·
      refine ⟨128071917756238304464630321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170762557008317739286173761 128071917756238304464630321)
      ·
        refine ⟨96053938317178728348472741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128071917756238304464630321 96053938317178728348472741)
        ·
          refine ⟨18010113434471011565338639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96053938317178728348472741 18010113434471011565338639)
          ·
            refine ⟨27015170151706517348007959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18010113434471011565338639 27015170151706517348007959)
            ·
              refine ⟨40522755227559776022011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27015170151706517348007959 40522755227559776022011939)
              ·
                refine ⟨60784132841339664033017909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40522755227559776022011939 60784132841339664033017909)
                ·
                  refine ⟨5698512453875593503095429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60784132841339664033017909 5698512453875593503095429)
                  ·
                    refine ⟨1068471085101673781830393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698512453875593503095429 1068471085101673781830393)
                    ·
                      rfl

theorem cell23_6242520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_6242520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242520 prefixEnd_6242520 := by exact prefixLift 6242520
  have htrace : WordTrace (prefixWord ++ tailWord_6242520) baseStart_6242520 baseEnd_6242520 := by
    simpa [prefixWord, tailWord_6242520, baseEnd_6242520] using wordTrace_append hprefix tailTrace_6242520
  have hstable : (prefixWord ++ tailWord_6242520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242520).length < 2 ^ (prefixWord ++ tailWord_6242520).sum := by decide
  have hdescent : baseEnd_6242520 < baseStart_6242520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242577 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_6242577 : Nat := 118140960795 + 6242577 * 2 ^ 59
def prefixEnd_6242577 : Nat := 4983230072969 + 3 ^ 40 * 6242577 * 2
def baseEnd_6242577 : Nat := 3205442523702327622478417

theorem tailTrace_6242577 : CollatzResearch.WordTrace tailWord_6242577 prefixEnd_6242577 3205442523702327622478417 := by
  unfold tailWord_6242577
  simp only [CollatzResearch.WordTrace]
  refine ⟨227685488305217151116389985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151790325536811434077593323 227685488305217151116389985)
  ·
    refine ⟨170764116228912863337292489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227685488305217151116389985 170764116228912863337292489)
    ·
      refine ⟨128073087171684647502969367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170764116228912863337292489 128073087171684647502969367)
      ·
        refine ⟨192109630757526971254454051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128073087171684647502969367 192109630757526971254454051)
        ·
          refine ⟨288164446136290456881681077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192109630757526971254454051 288164446136290456881681077)
          ·
            refine ⟨27015416825277230332657601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288164446136290456881681077 27015416825277230332657601)
            ·
              refine ⟨20261562618957922749493201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27015416825277230332657601 20261562618957922749493201)
              ·
                refine ⟨15196171964218442062119901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20261562618957922749493201 15196171964218442062119901)
                ·
                  refine ⟨5698564486581915773294963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15196171964218442062119901 5698564486581915773294963)
                  ·
                    refine ⟨8547846729872873659942445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698564486581915773294963 8547846729872873659942445)
                    ·
                      refine ⟨3205442523702327622478417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547846729872873659942445 3205442523702327622478417)
                      ·
                        rfl

theorem cell23_6242577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_6242577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242577 prefixEnd_6242577 := by exact prefixLift 6242577
  have htrace : WordTrace (prefixWord ++ tailWord_6242577) baseStart_6242577 baseEnd_6242577 := by
    simpa [prefixWord, tailWord_6242577, baseEnd_6242577] using wordTrace_append hprefix tailTrace_6242577
  have hstable : (prefixWord ++ tailWord_6242577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242577).length < 2 ^ (prefixWord ++ tailWord_6242577).sum := by decide
  have hdescent : baseEnd_6242577 < baseStart_6242577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242611 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 1, 1, 3]
def baseStart_6242611 : Nat := 118140960795 + 6242611 * 2 ^ 59
def prefixEnd_6242611 : Nat := 4983230072969 + 3 ^ 40 * 6242611 * 2
def baseEnd_6242611 : Nat := 3205459982044580489453261

theorem tailTrace_6242611 : CollatzResearch.WordTrace tailWord_6242611 prefixEnd_6242611 3205459982044580489453261 := by
  unfold tailWord_6242611
  simp only [CollatzResearch.WordTrace]
  refine ⟨227686728387093974923127687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151791152258062649948751791 227686728387093974923127687)
  ·
    refine ⟨341530092580640962384691531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227686728387093974923127687 341530092580640962384691531)
    ·
      refine ⟨512295138870961443577037297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341530092580640962384691531 512295138870961443577037297)
      ·
        refine ⟨384221354153221082682777973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512295138870961443577037297 384221354153221082682777973)
        ·
          refine ⟨36020751951864476501510435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 384221354153221082682777973 36020751951864476501510435)
          ·
            refine ⟨54031127927796714752265653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36020751951864476501510435 54031127927796714752265653)
            ·
              refine ⟨5065418243230942008024905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54031127927796714752265653 5065418243230942008024905)
              ·
                refine ⟨3799063682423206506018679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5065418243230942008024905 3799063682423206506018679)
                ·
                  refine ⟨5698595523634809759028019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799063682423206506018679 5698595523634809759028019)
                  ·
                    refine ⟨8547893285452214638542029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698595523634809759028019 8547893285452214638542029)
                    ·
                      refine ⟨3205459982044580489453261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8547893285452214638542029 3205459982044580489453261)
                      ·
                        rfl

theorem cell23_6242611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 1, 3].length) (baseStart_6242611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242611 prefixEnd_6242611 := by exact prefixLift 6242611
  have htrace : WordTrace (prefixWord ++ tailWord_6242611) baseStart_6242611 baseEnd_6242611 := by
    simpa [prefixWord, tailWord_6242611, baseEnd_6242611] using wordTrace_append hprefix tailTrace_6242611
  have hstable : (prefixWord ++ tailWord_6242611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242611).length < 2 ^ (prefixWord ++ tailWord_6242611).sum := by decide
  have hdescent : baseEnd_6242611 < baseStart_6242611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242620 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6242620 : Nat := 118140960795 + 6242620 * 2 ^ 59
def prefixEnd_6242620 : Nat := 4983230072969 + 3 ^ 40 * 6242620 * 2
def baseEnd_6242620 : Nat := 3205464603370470954240719

theorem tailTrace_6242620 : CollatzResearch.WordTrace tailWord_6242620 prefixEnd_6242620 3205464603370470954240719 := by
  unfold tailWord_6242620
  simp only [CollatzResearch.WordTrace]
  refine ⟨113843528322030684730102657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151791371096040912973470209 113843528322030684730102657)
  ·
    refine ⟨85382646241523013547576993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113843528322030684730102657 85382646241523013547576993)
    ·
      refine ⟨64036984681142260160682745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85382646241523013547576993 64036984681142260160682745)
      ·
        refine ⟨48027738510856695120512059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64036984681142260160682745 48027738510856695120512059)
        ·
          refine ⟨72041607766285042680768089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48027738510856695120512059 72041607766285042680768089)
          ·
            refine ⟨54031205824713782010576067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72041607766285042680768089 54031205824713782010576067)
            ·
              refine ⟨81046808737070673015864101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54031205824713782010576067 81046808737070673015864101)
              ·
                refine ⟨15196276638200751190474519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81046808737070673015864101 15196276638200751190474519)
                ·
                  refine ⟨22794414957301126785711779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15196276638200751190474519 22794414957301126785711779)
                  ·
                    refine ⟨34191622435951690178567669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22794414957301126785711779 34191622435951690178567669)
                    ·
                      refine ⟨3205464603370470954240719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34191622435951690178567669 3205464603370470954240719)
                      ·
                        rfl

theorem cell23_6242620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6242620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242620 prefixEnd_6242620 := by exact prefixLift 6242620
  have htrace : WordTrace (prefixWord ++ tailWord_6242620) baseStart_6242620 baseEnd_6242620 := by
    simpa [prefixWord, tailWord_6242620, baseEnd_6242620] using wordTrace_append hprefix tailTrace_6242620
  have hstable : (prefixWord ++ tailWord_6242620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242620).length < 2 ^ (prefixWord ++ tailWord_6242620).sum := by decide
  have hdescent : baseEnd_6242620 < baseStart_6242620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242668 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_6242668 : Nat := 118140960795 + 6242668 * 2 ^ 59
def prefixEnd_6242668 : Nat := 4983230072969 + 3 ^ 40 * 6242668 * 2
def baseEnd_6242668 : Nat := 3205489250441886766440499

theorem tailTrace_6242668 : CollatzResearch.WordTrace tailWord_6242668 prefixEnd_6242668 3205489250441886766440499 := by
  unfold tailWord_6242668
  simp only [CollatzResearch.WordTrace]
  refine ⟨113844403673943736828976329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151792538231924982438635105 113844403673943736828976329)
  ·
    refine ⟨85383302755457802621732247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113844403673943736828976329 85383302755457802621732247)
    ·
      refine ⟨128074954133186703932598371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85383302755457802621732247 128074954133186703932598371)
      ·
        refine ⟨192112431199780055898897557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128074954133186703932598371 192112431199780055898897557)
        ·
          refine ⟨9005270212489690120260823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192112431199780055898897557 9005270212489690120260823)
          ·
            refine ⟨13507905318734535180391235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005270212489690120260823 13507905318734535180391235)
            ·
              refine ⟨20261857978101802770586853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507905318734535180391235 20261857978101802770586853)
              ·
                refine ⟨3799098370894088019485035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20261857978101802770586853 3799098370894088019485035)
                ·
                  refine ⟨5698647556341132029227553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799098370894088019485035 5698647556341132029227553)
                  ·
                    refine ⟨4273985667255849021920665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5698647556341132029227553 4273985667255849021920665)
                    ·
                      refine ⟨3205489250441886766440499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4273985667255849021920665 3205489250441886766440499)
                      ·
                        rfl

theorem cell23_6242668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_6242668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242668 prefixEnd_6242668 := by exact prefixLift 6242668
  have htrace : WordTrace (prefixWord ++ tailWord_6242668) baseStart_6242668 baseEnd_6242668 := by
    simpa [prefixWord, tailWord_6242668, baseEnd_6242668] using wordTrace_append hprefix tailTrace_6242668
  have hstable : (prefixWord ++ tailWord_6242668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242668).length < 2 ^ (prefixWord ++ tailWord_6242668).sum := by decide
  have hdescent : baseEnd_6242668 < baseStart_6242668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242711 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_6242711 : Nat := 118140960795 + 6242711 * 2 ^ 59
def prefixEnd_6242711 : Nat := 4983230072969 + 3 ^ 40 * 6242711 * 2
def baseEnd_6242711 : Nat := 3205511330110030098202801

theorem tailTrace_6242711 : CollatzResearch.WordTrace tailWord_6242711 prefixEnd_6242711 3205511330110030098202801 := by
  unfold tailWord_6242711
  simp only [CollatzResearch.WordTrace]
  refine ⟨227690375686731692001767987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151793583791154461334511991 227690375686731692001767987)
  ·
    refine ⟨341535563530097538002651981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227690375686731692001767987 341535563530097538002651981)
    ·
      refine ⟨128075836323786576750994493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341535563530097538002651981 128075836323786576750994493)
      ·
        refine ⟨48028438621419966281622935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128075836323786576750994493 48028438621419966281622935)
        ·
          refine ⟨72042657932129949422434403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48028438621419966281622935 72042657932129949422434403)
          ·
            refine ⟨108063986898194924133651605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72042657932129949422434403 108063986898194924133651605)
            ·
              refine ⟨5065499385852887068764919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108063986898194924133651605 5065499385852887068764919)
              ·
                refine ⟨7598249078779330603147379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065499385852887068764919 7598249078779330603147379)
                ·
                  refine ⟨11397373618168995904721069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7598249078779330603147379 11397373618168995904721069)
                  ·
                    refine ⟨4274015106813373464270401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11397373618168995904721069 4274015106813373464270401)
                    ·
                      refine ⟨3205511330110030098202801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274015106813373464270401 3205511330110030098202801)
                      ·
                        rfl

theorem cell23_6242711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_6242711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242711 prefixEnd_6242711 := by exact prefixLift 6242711
  have htrace : WordTrace (prefixWord ++ tailWord_6242711) baseStart_6242711 baseEnd_6242711 := by
    simpa [prefixWord, tailWord_6242711, baseEnd_6242711] using wordTrace_append hprefix tailTrace_6242711
  have hstable : (prefixWord ++ tailWord_6242711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242711).length < 2 ^ (prefixWord ++ tailWord_6242711).sum := by decide
  have hdescent : baseEnd_6242711 < baseStart_6242711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242718 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6242718 : Nat := 118140960795 + 6242718 * 2 ^ 59
def prefixEnd_6242718 : Nat := 4983230072969 + 3 ^ 40 * 6242718 * 2
def baseEnd_6242718 : Nat := 3205514924474611570815269

theorem tailTrace_6242718 : CollatzResearch.WordTrace tailWord_6242718 prefixEnd_6242718 3205514924474611570815269 := by
  unfold tailWord_6242718
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461328874713291524659101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151793753998470888131515205 28461328874713291524659101)
  ·
    refine ⟨10672998328017484321747163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28461328874713291524659101 10672998328017484321747163)
    ·
      refine ⟨16009497492026226482620745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672998328017484321747163 16009497492026226482620745)
      ·
        refine ⟨12007123119019669861965559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16009497492026226482620745 12007123119019669861965559)
        ·
          refine ⟨18010684678529504792948339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007123119019669861965559 18010684678529504792948339)
          ·
            refine ⟨27016027017794257189422509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18010684678529504792948339 27016027017794257189422509)
            ·
              refine ⟨10131010131672846446033441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27016027017794257189422509 10131010131672846446033441)
              ·
                refine ⟨7598257598754634834525081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131010131672846446033441 7598257598754634834525081)
                ·
                  refine ⟨5698693199065976125893811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7598257598754634834525081 5698693199065976125893811)
                  ·
                    refine ⟨8548039798598964188840717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698693199065976125893811 8548039798598964188840717)
                    ·
                      refine ⟨3205514924474611570815269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548039798598964188840717 3205514924474611570815269)
                      ·
                        rfl

theorem cell23_6242718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6242718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242718 prefixEnd_6242718 := by exact prefixLift 6242718
  have htrace : WordTrace (prefixWord ++ tailWord_6242718) baseStart_6242718 baseEnd_6242718 := by
    simpa [prefixWord, tailWord_6242718, baseEnd_6242718] using wordTrace_append hprefix tailTrace_6242718
  have hstable : (prefixWord ++ tailWord_6242718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242718).length < 2 ^ (prefixWord ++ tailWord_6242718).sum := by decide
  have hdescent : baseEnd_6242718 < baseStart_6242718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242737 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6242737 : Nat := 118140960795 + 6242737 * 2 ^ 59
def prefixEnd_6242737 : Nat := 4983230072969 + 3 ^ 40 * 6242737 * 2
def baseEnd_6242737 : Nat := 3205524680607046996477681

theorem tailTrace_6242737 : CollatzResearch.WordTrace tailWord_6242737 prefixEnd_6242737 3205524680607046996477681 := by
  unfold tailWord_6242737
  simp only [CollatzResearch.WordTrace]
  refine ⟨227691323984637498442214465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151794215989758332294809643 227691323984637498442214465)
  ·
    refine ⟨170768492988478123831660849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227691323984637498442214465 170768492988478123831660849)
    ·
      refine ⟨128076369741358592873745637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170768492988478123831660849 128076369741358592873745637)
      ·
        refine ⟨24014319326504736163827307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128076369741358592873745637 24014319326504736163827307)
        ·
          refine ⟨36021478989757104245740961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24014319326504736163827307 36021478989757104245740961)
          ·
            refine ⟨27016109242317828184305721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36021478989757104245740961 27016109242317828184305721)
            ·
              refine ⟨20262081931738371138229291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27016109242317828184305721 20262081931738371138229291)
              ·
                refine ⟨30393122897607556707343937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20262081931738371138229291 30393122897607556707343937)
                ·
                  refine ⟨22794842173205667530507953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30393122897607556707343937 22794842173205667530507953)
                  ·
                    refine ⟨17096131629904250647880965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22794842173205667530507953 17096131629904250647880965)
                    ·
                      refine ⟨3205524680607046996477681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17096131629904250647880965 3205524680607046996477681)
                      ·
                        rfl

theorem cell23_6242737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6242737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242737 prefixEnd_6242737 := by exact prefixLift 6242737
  have htrace : WordTrace (prefixWord ++ tailWord_6242737) baseStart_6242737 baseEnd_6242737 := by
    simpa [prefixWord, tailWord_6242737, baseEnd_6242737] using wordTrace_append hprefix tailTrace_6242737
  have hstable : (prefixWord ++ tailWord_6242737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242737).length < 2 ^ (prefixWord ++ tailWord_6242737).sum := by decide
  have hdescent : baseEnd_6242737 < baseStart_6242737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242767 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 7, 2]
def baseStart_6242767 : Nat := 118140960795 + 6242767 * 2 ^ 59
def prefixEnd_6242767 : Nat := 4983230072969 + 3 ^ 40 * 6242767 * 2
def baseEnd_6242767 : Nat := 3205540085026681879102543

theorem tailTrace_6242767 : CollatzResearch.WordTrace tailWord_6242767 prefixEnd_6242767 3205540085026681879102543 := by
  unfold tailWord_6242767
  simp only [CollatzResearch.WordTrace]
  refine ⟨227692418174528813565806555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151794945449685875710537703 227692418174528813565806555)
  ·
    refine ⟨341538627261793220348709833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227692418174528813565806555 341538627261793220348709833)
    ·
      refine ⟨256153970446344915261532375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341538627261793220348709833 256153970446344915261532375)
      ·
        refine ⟨384230955669517372892298563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256153970446344915261532375 384230955669517372892298563)
        ·
          refine ⟨576346433504276059338447845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384230955669517372892298563 576346433504276059338447845)
          ·
            refine ⟨108064956282051761125958971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576346433504276059338447845 108064956282051761125958971)
            ·
              refine ⟨162097434423077641688938457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108064956282051761125958971 162097434423077641688938457)
              ·
                refine ⟨121573075817308231266703843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162097434423077641688938457 121573075817308231266703843)
                ·
                  refine ⟨182359613725962346900055765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121573075817308231266703843 182359613725962346900055765)
                  ·
                    refine ⟨4274053446702242505470057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182359613725962346900055765 4274053446702242505470057)
                    ·
                      refine ⟨3205540085026681879102543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274053446702242505470057 3205540085026681879102543)
                      ·
                        rfl

theorem cell23_6242767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 7, 2].length) (baseStart_6242767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242767 prefixEnd_6242767 := by exact prefixLift 6242767
  have htrace : WordTrace (prefixWord ++ tailWord_6242767) baseStart_6242767 baseEnd_6242767 := by
    simpa [prefixWord, tailWord_6242767, baseEnd_6242767] using wordTrace_append hprefix tailTrace_6242767
  have hstable : (prefixWord ++ tailWord_6242767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242767).length < 2 ^ (prefixWord ++ tailWord_6242767).sum := by decide
  have hdescent : baseEnd_6242767 < baseStart_6242767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242777 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_6242777 : Nat := 118140960795 + 6242777 * 2 ^ 59
def prefixEnd_6242777 : Nat := 4983230072969 + 3 ^ 40 * 6242777 * 2
def baseEnd_6242777 : Nat := 1068515073277742279992499

theorem tailTrace_6242777 : CollatzResearch.WordTrace tailWord_6242777 prefixEnd_6242777 1068515073277742279992499 := by
  unfold tailWord_6242777
  simp only [CollatzResearch.WordTrace]
  refine ⟨227692782904492585273670585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151795188602995056849113723 227692782904492585273670585)
  ·
    refine ⟨170769587178369438955252939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227692782904492585273670585 170769587178369438955252939)
    ·
      refine ⟨256154380767554158432879409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170769587178369438955252939 256154380767554158432879409)
      ·
        refine ⟨192115785575665618824659557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256154380767554158432879409 192115785575665618824659557)
        ·
          refine ⟨36021709795437303529623667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192115785575665618824659557 36021709795437303529623667)
          ·
            refine ⟨54032564693155955294435501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36021709795437303529623667 54032564693155955294435501)
            ·
              refine ⟨20262211759933483235413313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54032564693155955294435501 20262211759933483235413313)
              ·
                refine ⟨15196658819950112426559985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20262211759933483235413313 15196658819950112426559985)
                ·
                  refine ⟨11397494114962584319919989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15196658819950112426559985 11397494114962584319919989)
                  ·
                    refine ⟨1068515073277742279992499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11397494114962584319919989 1068515073277742279992499)
                    ·
                      rfl

theorem cell23_6242777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_6242777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242777 prefixEnd_6242777 := by exact prefixLift 6242777
  have htrace : WordTrace (prefixWord ++ tailWord_6242777) baseStart_6242777 baseEnd_6242777 := by
    simpa [prefixWord, tailWord_6242777, baseEnd_6242777] using wordTrace_append hprefix tailTrace_6242777
  have hstable : (prefixWord ++ tailWord_6242777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242777).length < 2 ^ (prefixWord ++ tailWord_6242777).sum := by decide
  have hdescent : baseEnd_6242777 < baseStart_6242777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242781 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 5]
def baseStart_6242781 : Nat := 118140960795 + 6242781 * 2 ^ 59
def prefixEnd_6242781 : Nat := 4983230072969 + 3 ^ 40 * 6242781 * 2
def baseEnd_6242781 : Nat := 356171919306204980480831

theorem tailTrace_6242781 : CollatzResearch.WordTrace tailWord_6242781 prefixEnd_6242781 356171919306204980480831 := by
  unfold tailWord_6242781
  simp only [CollatzResearch.WordTrace]
  refine ⟨227692928796478093956816197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151795285864318729304544131 227692928796478093956816197)
  ·
    refine ⟨42692424149339642616903037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227692928796478093956816197 42692424149339642616903037)
    ·
      refine ⟨16009659056002365981338639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42692424149339642616903037 16009659056002365981338639)
      ·
        refine ⟨24014488584003548972007959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16009659056002365981338639 24014488584003548972007959)
        ·
          refine ⟨36021732876005323458011939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24014488584003548972007959 36021732876005323458011939)
          ·
            refine ⟨54032599314007985187017909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36021732876005323458011939 54032599314007985187017909)
            ·
              refine ⟨5065556185688248611282929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54032599314007985187017909 5065556185688248611282929)
              ·
                refine ⟨3799167139266186458462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5065556185688248611282929 3799167139266186458462197)
                ·
                  refine ⟨356171919306204980480831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799167139266186458462197 356171919306204980480831)
                  ·
                    rfl

theorem cell23_6242781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_6242781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242781 prefixEnd_6242781 := by exact prefixLift 6242781
  have htrace : WordTrace (prefixWord ++ tailWord_6242781) baseStart_6242781 baseEnd_6242781 := by
    simpa [prefixWord, tailWord_6242781, baseEnd_6242781] using wordTrace_append hprefix tailTrace_6242781
  have hstable : (prefixWord ++ tailWord_6242781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242781).length < 2 ^ (prefixWord ++ tailWord_6242781).sum := by decide
  have hdescent : baseEnd_6242781 < baseStart_6242781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242847 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_6242847 : Nat := 118140960795 + 6242847 * 2 ^ 59
def prefixEnd_6242847 : Nat := 4983230072969 + 3 ^ 40 * 6242847 * 2
def baseEnd_6242847 : Nat := 3205581163479041566102175

theorem tailTrace_6242847 : CollatzResearch.WordTrace tailWord_6242847 prefixEnd_6242847 3205581163479041566102175 := by
  unfold tailWord_6242847
  simp only [CollatzResearch.WordTrace]
  refine ⟨227695336014238987228718795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151796890676159324819145863 227695336014238987228718795)
  ·
    refine ⟨341543004021358480843078193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227695336014238987228718795 341543004021358480843078193)
    ·
      refine ⟨256157253016018860632308645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341543004021358480843078193 256157253016018860632308645)
      ·
        refine ⟨48029484940503536368557871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256157253016018860632308645 48029484940503536368557871)
        ·
          refine ⟨72044227410755304552836807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48029484940503536368557871 72044227410755304552836807)
          ·
            refine ⟨108066341116132956829255211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72044227410755304552836807 108066341116132956829255211)
            ·
              refine ⟨162099511674199435243882817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108066341116132956829255211 162099511674199435243882817)
              ·
                refine ⟨121574633755649576432912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162099511674199435243882817 121574633755649576432912113)
                ·
                  refine ⟨91180975316737182324684085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121574633755649576432912113 91180975316737182324684085)
                  ·
                    refine ⟨8548216435944110842939133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91180975316737182324684085 8548216435944110842939133)
                    ·
                      refine ⟨3205581163479041566102175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548216435944110842939133 3205581163479041566102175)
                      ·
                        rfl

theorem cell23_6242847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_6242847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242847 prefixEnd_6242847 := by exact prefixLift 6242847
  have htrace : WordTrace (prefixWord ++ tailWord_6242847) baseStart_6242847 baseEnd_6242847 := by
    simpa [prefixWord, tailWord_6242847, baseEnd_6242847] using wordTrace_append hprefix tailTrace_6242847
  have hstable : (prefixWord ++ tailWord_6242847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242847).length < 2 ^ (prefixWord ++ tailWord_6242847).sum := by decide
  have hdescent : baseEnd_6242847 < baseStart_6242847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242864 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_6242864 : Nat := 118140960795 + 6242864 * 2 ^ 59
def prefixEnd_6242864 : Nat := 4983230072969 + 3 ^ 40 * 6242864 * 2
def baseEnd_6242864 : Nat := 3205589892650167999589597

theorem tailTrace_6242864 : CollatzResearch.WordTrace tailWord_6242864 prefixEnd_6242864 3205589892650167999589597 := by
  unfold tailWord_6242864
  simp only [CollatzResearch.WordTrace]
  refine ⟨113847978027588699566043823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151797304036784932754725097 113847978027588699566043823)
  ·
    refine ⟨170771967041383049349065735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113847978027588699566043823 170771967041383049349065735)
    ·
      refine ⟨256157950562074574023598603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170771967041383049349065735 256157950562074574023598603)
      ·
        refine ⟨384236925843111861035397905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256157950562074574023598603 384236925843111861035397905)
        ·
          refine ⟨288177694382333895776548429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384236925843111861035397905 288177694382333895776548429)
          ·
            refine ⟨108066635393375210916205661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288177694382333895776548429 108066635393375210916205661)
            ·
              refine ⟨40524988272515704093577123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108066635393375210916205661 40524988272515704093577123)
              ·
                refine ⟨60787482408773556140365685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40524988272515704093577123 60787482408773556140365685)
                ·
                  refine ⟨5698826475822520888159283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60787482408773556140365685 5698826475822520888159283)
                  ·
                    refine ⟨8548239713733781332238925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698826475822520888159283 8548239713733781332238925)
                    ·
                      refine ⟨3205589892650167999589597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548239713733781332238925 3205589892650167999589597)
                      ·
                        rfl

theorem cell23_6242864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_6242864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242864 prefixEnd_6242864 := by exact prefixLift 6242864
  have htrace : WordTrace (prefixWord ++ tailWord_6242864) baseStart_6242864 baseEnd_6242864 := by
    simpa [prefixWord, tailWord_6242864, baseEnd_6242864] using wordTrace_append hprefix tailTrace_6242864
  have hstable : (prefixWord ++ tailWord_6242864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242864).length < 2 ^ (prefixWord ++ tailWord_6242864).sum := by decide
  have hdescent : baseEnd_6242864 < baseStart_6242864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242867 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 3, 5]
def baseStart_6242867 : Nat := 118140960795 + 6242867 * 2 ^ 59
def prefixEnd_6242867 : Nat := 4983230072969 + 3 ^ 40 * 6242867 * 2
def baseEnd_6242867 : Nat := 1068530477697377162617361

theorem tailTrace_6242867 : CollatzResearch.WordTrace tailWord_6242867 prefixEnd_6242867 1068530477697377162617361 := by
  unfold tailWord_6242867
  simp only [CollatzResearch.WordTrace]
  refine ⟨227696065474166530644446855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151797376982777687096297903 227696065474166530644446855)
  ·
    refine ⟨341544098211249795966670283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227696065474166530644446855 341544098211249795966670283)
    ·
      refine ⟨512316147316874693950005425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341544098211249795966670283 512316147316874693950005425)
      ·
        refine ⟨384237110487656020462504069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512316147316874693950005425 384237110487656020462504069)
        ·
          refine ⟨72044458216435503836719513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384237110487656020462504069 72044458216435503836719513)
          ·
            refine ⟨54033343662326627877539635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72044458216435503836719513 54033343662326627877539635)
            ·
              refine ⟨81050015493489941816309453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54033343662326627877539635 81050015493489941816309453)
              ·
                refine ⟨30393755810058728181116045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81050015493489941816309453 30393755810058728181116045)
                ·
                  refine ⟨11397658428772023067918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30393755810058728181116045 11397658428772023067918517)
                  ·
                    refine ⟨1068530477697377162617361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11397658428772023067918517 1068530477697377162617361)
                    ·
                      rfl

theorem cell23_6242867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].length) (baseStart_6242867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242867 prefixEnd_6242867 := by exact prefixLift 6242867
  have htrace : WordTrace (prefixWord ++ tailWord_6242867) baseStart_6242867 baseEnd_6242867 := by
    simpa [prefixWord, tailWord_6242867, baseEnd_6242867] using wordTrace_append hprefix tailTrace_6242867
  have hstable : (prefixWord ++ tailWord_6242867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242867).length < 2 ^ (prefixWord ++ tailWord_6242867).sum := by decide
  have hdescent : baseEnd_6242867 < baseStart_6242867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242868 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6242868 : Nat := 118140960795 + 6242868 * 2 ^ 59
def prefixEnd_6242868 : Nat := 4983230072969 + 3 ^ 40 * 6242868 * 2
def baseEnd_6242868 : Nat := 3205591946572785983939579

theorem tailTrace_6242868 : CollatzResearch.WordTrace tailWord_6242868 prefixEnd_6242868 3205591946572785983939579 := by
  unfold tailWord_6242868
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848050973581453907616629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151797401298108605210155505 113848050973581453907616629)
  ·
    refine ⟨10673254778773261303839059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113848050973581453907616629 10673254778773261303839059)
    ·
      refine ⟨16009882168159891955758589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673254778773261303839059 16009882168159891955758589)
      ·
        refine ⟨6003705813059959483409471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16009882168159891955758589 6003705813059959483409471)
        ·
          refine ⟨9005558719589939225114207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003705813059959483409471 9005558719589939225114207)
          ·
            refine ⟨13508338079384908837671311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005558719589939225114207 13508338079384908837671311)
            ·
              refine ⟨20262507119077363256506967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13508338079384908837671311 20262507119077363256506967)
              ·
                refine ⟨30393760678616044884760451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20262507119077363256506967 30393760678616044884760451)
                ·
                  refine ⟨45590641017924067327140677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30393760678616044884760451 45590641017924067327140677)
                  ·
                    refine ⟨8548245190860762623838877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45590641017924067327140677 8548245190860762623838877)
                    ·
                      refine ⟨3205591946572785983939579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548245190860762623838877 3205591946572785983939579)
                      ·
                        rfl

theorem cell23_6242868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6242868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242868 prefixEnd_6242868 := by exact prefixLift 6242868
  have htrace : WordTrace (prefixWord ++ tailWord_6242868) baseStart_6242868 baseEnd_6242868 := by
    simpa [prefixWord, tailWord_6242868, baseEnd_6242868] using wordTrace_append hprefix tailTrace_6242868
  have hstable : (prefixWord ++ tailWord_6242868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242868).length < 2 ^ (prefixWord ++ tailWord_6242868).sum := by decide
  have hdescent : baseEnd_6242868 < baseStart_6242868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242898 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_6242898 : Nat := 118140960795 + 6242898 * 2 ^ 59
def prefixEnd_6242898 : Nat := 4983230072969 + 3 ^ 40 * 6242898 * 2
def baseEnd_6242898 : Nat := 3205607350992420866564441

theorem tailTrace_6242898 : CollatzResearch.WordTrace tailWord_6242898 prefixEnd_6242898 3205607350992420866564441 := by
  unfold tailWord_6242898
  simp only [CollatzResearch.WordTrace]
  refine ⟨56924299034263555734706337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151798130758036148625883565 56924299034263555734706337)
  ·
    refine ⟨42693224275697666801029753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56924299034263555734706337 42693224275697666801029753)
    ·
      refine ⟨32019918206773250100772315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42693224275697666801029753 32019918206773250100772315)
      ·
        refine ⟨48029877310159875151158473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32019918206773250100772315 48029877310159875151158473)
        ·
          refine ⟨36022407982619906363368855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48029877310159875151158473 36022407982619906363368855)
          ·
            refine ⟨54033611973929859545053283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36022407982619906363368855 54033611973929859545053283)
            ·
              refine ⟨81050417960894789317579925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54033611973929859545053283 81050417960894789317579925)
              ·
                refine ⟨3799238341916943249261559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81050417960894789317579925 3799238341916943249261559)
                ·
                  refine ⟨5698857512875414873892339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799238341916943249261559 5698857512875414873892339)
                  ·
                    refine ⟨8548286269313122310838509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698857512875414873892339 8548286269313122310838509)
                    ·
                      refine ⟨3205607350992420866564441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548286269313122310838509 3205607350992420866564441)
                      ·
                        rfl

theorem cell23_6242898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_6242898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242898 prefixEnd_6242898 := by exact prefixLift 6242898
  have htrace : WordTrace (prefixWord ++ tailWord_6242898) baseStart_6242898 baseEnd_6242898 := by
    simpa [prefixWord, tailWord_6242898, baseEnd_6242898] using wordTrace_append hprefix tailTrace_6242898
  have hstable : (prefixWord ++ tailWord_6242898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242898).length < 2 ^ (prefixWord ++ tailWord_6242898).sum := by decide
  have hdescent : baseEnd_6242898 < baseStart_6242898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242924 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_6242924 : Nat := 118140960795 + 6242924 * 2 ^ 59
def prefixEnd_6242924 : Nat := 4983230072969 + 3 ^ 40 * 6242924 * 2
def baseEnd_6242924 : Nat := 3205620701489437764839321

theorem tailTrace_6242924 : CollatzResearch.WordTrace tailWord_6242924 prefixEnd_6242924 3205620701489437764839321 := by
  unfold tailWord_6242924
  simp only [CollatzResearch.WordTrace]
  refine ⟨113849072217480014689635913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151798762956640019586181217 113849072217480014689635913)
  ·
    refine ⟨85386804163110011017226935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113849072217480014689635913 85386804163110011017226935)
    ·
      refine ⟨128080206244665016525840403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85386804163110011017226935 128080206244665016525840403)
      ·
        refine ⟨192120309366997524788760605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128080206244665016525840403 192120309366997524788760605)
        ·
          refine ⟨72045116012624071795785227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192120309366997524788760605 72045116012624071795785227)
          ·
            refine ⟨108067674018936107693677841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72045116012624071795785227 108067674018936107693677841)
            ·
              refine ⟨81050755514202080770258381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108067674018936107693677841 81050755514202080770258381)
              ·
                refine ⟨30394033317825780288846893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81050755514202080770258381 30394033317825780288846893)
                ·
                  refine ⟨11397762494184667608317585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30394033317825780288846893 11397762494184667608317585)
                  ·
                    refine ⟨8548321870638500706238189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11397762494184667608317585 8548321870638500706238189)
                    ·
                      refine ⟨3205620701489437764839321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8548321870638500706238189 3205620701489437764839321)
                      ·
                        rfl

theorem cell23_6242924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_6242924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242924 prefixEnd_6242924 := by exact prefixLift 6242924
  have htrace : WordTrace (prefixWord ++ tailWord_6242924) baseStart_6242924 baseEnd_6242924 := by
    simpa [prefixWord, tailWord_6242924, baseEnd_6242924] using wordTrace_append hprefix tailTrace_6242924
  have hstable : (prefixWord ++ tailWord_6242924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242924).length < 2 ^ (prefixWord ++ tailWord_6242924).sum := by decide
  have hdescent : baseEnd_6242924 < baseStart_6242924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242941 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_6242941 : Nat := 118140960795 + 6242941 * 2 ^ 59
def prefixEnd_6242941 : Nat := 4983230072969 + 3 ^ 40 * 6242941 * 2
def baseEnd_6242941 : Nat := 3205629430660564198326743

theorem tailTrace_6242941 : CollatzResearch.WordTrace tailWord_6242941 prefixEnd_6242941 3205629430660564198326743 := by
  unfold tailWord_6242941
  simp only [CollatzResearch.WordTrace]
  refine ⟨227698764475898441282640677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151799176317265627521760451 227698764475898441282640677)
  ·
    refine ⟨42693518339230957740495127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227698764475898441282640677 42693518339230957740495127)
    ·
      refine ⟨64040277508846436610742691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42693518339230957740495127 64040277508846436610742691)
      ·
        refine ⟨96060416263269654916114037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64040277508846436610742691 96060416263269654916114037)
        ·
          refine ⟨9005664024681530148385691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96060416263269654916114037 9005664024681530148385691)
          ·
            refine ⟨13508496037022295222578537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005664024681530148385691 13508496037022295222578537)
            ·
              refine ⟨10131372027766721416933903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13508496037022295222578537 10131372027766721416933903)
              ·
                refine ⟨15197058041650082125400855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10131372027766721416933903 15197058041650082125400855)
                ·
                  refine ⟨22795587062475123188101283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15197058041650082125400855 22795587062475123188101283)
                  ·
                    refine ⟨34193380593712684782151925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22795587062475123188101283 34193380593712684782151925)
                    ·
                      refine ⟨3205629430660564198326743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34193380593712684782151925 3205629430660564198326743)
                      ·
                        rfl

theorem cell23_6242941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_6242941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6242941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6242941 prefixEnd_6242941 := by exact prefixLift 6242941
  have htrace : WordTrace (prefixWord ++ tailWord_6242941) baseStart_6242941 baseEnd_6242941 := by
    simpa [prefixWord, tailWord_6242941, baseEnd_6242941] using wordTrace_append hprefix tailTrace_6242941
  have hstable : (prefixWord ++ tailWord_6242941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242941).length < 2 ^ (prefixWord ++ tailWord_6242941).sum := by decide
  have hdescent : baseEnd_6242941 < baseStart_6242941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243004 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_6243004 : Nat := 118140960795 + 6243004 * 2 ^ 59
def prefixEnd_6243004 : Nat := 4983230072969 + 3 ^ 40 * 6243004 * 2
def baseEnd_6243004 : Nat := 1068553926647265817279651

theorem tailTrace_6243004 : CollatzResearch.WordTrace tailWord_6243004 prefixEnd_6243004 1068553926647265817279651 := by
  unfold tailWord_6243004
  simp only [CollatzResearch.WordTrace]
  refine ⟨113850531137335101521092033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151800708183113468694789377 113850531137335101521092033)
  ·
    refine ⟨85387898353001326140819025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113850531137335101521092033 85387898353001326140819025)
    ·
      refine ⟨64040923764750994605614269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85387898353001326140819025 64040923764750994605614269)
      ·
        refine ⟨24015346411781622977105351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64040923764750994605614269 24015346411781622977105351)
        ·
          refine ⟨36023019617672434465658027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24015346411781622977105351 36023019617672434465658027)
          ·
            refine ⟨54034529426508651698487041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36023019617672434465658027 54034529426508651698487041)
            ·
              refine ⟨40525897069881488773865281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54034529426508651698487041 40525897069881488773865281)
              ·
                refine ⟨30394422802411116580398961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40525897069881488773865281 30394422802411116580398961)
                ·
                  refine ⟨22795817101808337435299221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30394422802411116580398961 22795817101808337435299221)
                  ·
                    refine ⟨1068553926647265817279651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22795817101808337435299221 1068553926647265817279651)
                    ·
                      rfl

theorem cell23_6243004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_6243004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243004 prefixEnd_6243004 := by exact prefixLift 6243004
  have htrace : WordTrace (prefixWord ++ tailWord_6243004) baseStart_6243004 baseEnd_6243004 := by
    simpa [prefixWord, tailWord_6243004, baseEnd_6243004] using wordTrace_append hprefix tailTrace_6243004
  have hstable : (prefixWord ++ tailWord_6243004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243004).length < 2 ^ (prefixWord ++ tailWord_6243004).sum := by decide
  have hdescent : baseEnd_6243004 < baseStart_6243004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243017 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 13]
def baseStart_6243017 : Nat := 118140960795 + 6243017 * 2 ^ 59
def prefixEnd_6243017 : Nat := 4983230072969 + 3 ^ 40 * 6243017 * 2
def baseEnd_6243017 : Nat := 356185383910033988997377

theorem tailTrace_6243017 : CollatzResearch.WordTrace tailWord_6243017 prefixEnd_6243017 356185383910033988997377 := by
  unfold tailWord_6243017
  simp only [CollatzResearch.WordTrace]
  refine ⟨227701536423623106262407305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151801024282415404174938203 227701536423623106262407305)
  ·
    refine ⟨170776152317717329696805479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227701536423623106262407305 170776152317717329696805479)
    ·
      refine ⟨256164228476575994545208219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170776152317717329696805479 256164228476575994545208219)
      ·
        refine ⟨384246342714863991817812329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256164228476575994545208219 384246342714863991817812329)
        ·
          refine ⟨288184757036147993863359247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384246342714863991817812329 288184757036147993863359247)
          ·
            refine ⟨432277135554221990795038871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288184757036147993863359247 432277135554221990795038871)
            ·
              refine ⟨648415703331332986192558307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432277135554221990795038871 648415703331332986192558307)
              ·
                refine ⟨972623554996999479288837461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648415703331332986192558307 972623554996999479288837461)
                ·
                  refine ⟨356185383910033988997377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 972623554996999479288837461 356185383910033988997377)
                  ·
                    rfl

theorem cell23_6243017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_6243017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243017 prefixEnd_6243017 := by exact prefixLift 6243017
  have htrace : WordTrace (prefixWord ++ tailWord_6243017) baseStart_6243017 baseEnd_6243017 := by
    simpa [prefixWord, tailWord_6243017, baseEnd_6243017] using wordTrace_append hprefix tailTrace_6243017
  have hstable : (prefixWord ++ tailWord_6243017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243017).length < 2 ^ (prefixWord ++ tailWord_6243017).sum := by decide
  have hdescent : baseEnd_6243017 < baseStart_6243017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243034 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_6243034 : Nat := 118140960795 + 6243034 * 2 ^ 59
def prefixEnd_6243034 : Nat := 4983230072969 + 3 ^ 40 * 6243034 * 2
def baseEnd_6243034 : Nat := 356186353817936926051535

theorem tailTrace_6243034 : CollatzResearch.WordTrace tailWord_6243034 prefixEnd_6243034 356186353817936926051535 := by
  unfold tailWord_6243034
  simp only [CollatzResearch.WordTrace]
  refine ⟨56925539116140379541444039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151801437643041012110517437 56925539116140379541444039)
  ·
    refine ⟨85388308674210569312166059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56925539116140379541444039 85388308674210569312166059)
    ·
      refine ⟨128082463011315853968249089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85388308674210569312166059 128082463011315853968249089)
      ·
        refine ⟨96061847258486890476186817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128082463011315853968249089 96061847258486890476186817)
        ·
          refine ⟨72046385443865167857140113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96061847258486890476186817 72046385443865167857140113)
          ·
            refine ⟨54034789082898875892855085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72046385443865167857140113 54034789082898875892855085)
            ·
              refine ⟨20263045906087078459820657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54034789082898875892855085 20263045906087078459820657)
              ·
                refine ⟨15197284429565308844865493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20263045906087078459820657 15197284429565308844865493)
                ·
                  refine ⟨356186353817936926051535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15197284429565308844865493 356186353817936926051535)
                  ·
                    rfl

theorem cell23_6243034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_6243034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243034 prefixEnd_6243034 := by exact prefixLift 6243034
  have htrace : WordTrace (prefixWord ++ tailWord_6243034) baseStart_6243034 baseEnd_6243034 := by
    simpa [prefixWord, tailWord_6243034, baseEnd_6243034] using wordTrace_append hprefix tailTrace_6243034
  have hstable : (prefixWord ++ tailWord_6243034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243034).length < 2 ^ (prefixWord ++ tailWord_6243034).sum := by decide
  have hdescent : baseEnd_6243034 < baseStart_6243034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243064 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_6243064 : Nat := 118140960795 + 6243064 * 2 ^ 59
def prefixEnd_6243064 : Nat := 4983230072969 + 3 ^ 40 * 6243064 * 2
def baseEnd_6243064 : Nat := 1068564196260355739029559

theorem tailTrace_6243064 : CollatzResearch.WordTrace tailWord_6243064 prefixEnd_6243064 1068564196260355739029559 := by
  unfold tailWord_6243064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113851625327226416644684123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151802167102968555526245497 113851625327226416644684123)
  ·
    refine ⟨170777437990839624967026185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113851625327226416644684123 170777437990839624967026185)
    ·
      refine ⟨128083078493129718725269639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170777437990839624967026185 128083078493129718725269639)
      ·
        refine ⟨192124617739694578087904459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128083078493129718725269639 192124617739694578087904459)
        ·
          refine ⟨288186926609541867131856689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192124617739694578087904459 288186926609541867131856689)
          ·
            refine ⟨216140194957156400348892517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288186926609541867131856689 216140194957156400348892517)
            ·
              refine ⟨40526286554466825065417347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216140194957156400348892517 40526286554466825065417347)
              ·
                refine ⟨60789429831700237598126021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40526286554466825065417347 60789429831700237598126021)
                ·
                  refine ⟨11398018093443794549648629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60789429831700237598126021 11398018093443794549648629)
                  ·
                    refine ⟨1068564196260355739029559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11398018093443794549648629 1068564196260355739029559)
                    ·
                      rfl

theorem cell23_6243064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_6243064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243064 prefixEnd_6243064 := by exact prefixLift 6243064
  have htrace : WordTrace (prefixWord ++ tailWord_6243064) baseStart_6243064 baseEnd_6243064 := by
    simpa [prefixWord, tailWord_6243064, baseEnd_6243064] using wordTrace_append hprefix tailTrace_6243064
  have hstable : (prefixWord ++ tailWord_6243064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243064).length < 2 ^ (prefixWord ++ tailWord_6243064).sum := by decide
  have hdescent : baseEnd_6243064 < baseStart_6243064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243118 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6243118 : Nat := 118140960795 + 6243118 * 2 ^ 59
def prefixEnd_6243118 : Nat := 4983230072969 + 3 ^ 40 * 6243118 * 2
def baseEnd_6243118 : Nat := 3205720316736410005813429

theorem tailTrace_6243118 : CollatzResearch.WordTrace tailWord_6243118 prefixEnd_6243118 3205720316736410005813429 := by
  unfold tailWord_6243118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28463152524532150063979251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151803480130838133674556005 28463152524532150063979251)
  ·
    refine ⟨42694728786798225095968877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28463152524532150063979251 42694728786798225095968877)
    ·
      refine ⟨16010523295049334410988329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42694728786798225095968877 16010523295049334410988329)
      ·
        refine ⟨12007892471287000808241247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16010523295049334410988329 12007892471287000808241247)
        ·
          refine ⟨18011838706930501212361871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007892471287000808241247 18011838706930501212361871)
          ·
            refine ⟨27017758060395751818542807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18011838706930501212361871 27017758060395751818542807)
            ·
              refine ⟨40526637090593627727814211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27017758060395751818542807 40526637090593627727814211)
              ·
                refine ⟨60789955635890441591721317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40526637090593627727814211 60789955635890441591721317)
                ·
                  refine ⟨11398116681729457798447747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60789955635890441591721317 11398116681729457798447747)
                  ·
                    refine ⟨17097175022594186697671621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11398116681729457798447747 17097175022594186697671621)
                    ·
                      refine ⟨3205720316736410005813429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17097175022594186697671621 3205720316736410005813429)
                      ·
                        rfl

theorem cell23_6243118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6243118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243118 prefixEnd_6243118 := by exact prefixLift 6243118
  have htrace : WordTrace (prefixWord ++ tailWord_6243118) baseStart_6243118 baseEnd_6243118 := by
    simpa [prefixWord, tailWord_6243118, baseEnd_6243118] using wordTrace_append hprefix tailTrace_6243118
  have hstable : (prefixWord ++ tailWord_6243118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243118).length < 2 ^ (prefixWord ++ tailWord_6243118).sum := by decide
  have hdescent : baseEnd_6243118 < baseStart_6243118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243208 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6243208 : Nat := 118140960795 + 6243208 * 2 ^ 59
def prefixEnd_6243208 : Nat := 4983230072969 + 3 ^ 40 * 6243208 * 2
def baseEnd_6243208 : Nat := 3205766529995314653688015

theorem tailTrace_6243208 : CollatzResearch.WordTrace tailWord_6243208 prefixEnd_6243208 3205766529995314653688015 := by
  unfold tailWord_6243208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113854251382965572941305139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151805668510620763921740185 113854251382965572941305139)
  ·
    refine ⟨170781377074448359411957709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113854251382965572941305139 170781377074448359411957709)
    ·
      refine ⟨64043016402918134779484141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170781377074448359411957709 64043016402918134779484141)
      ·
        refine ⟨24016131151094300542306553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64043016402918134779484141 24016131151094300542306553)
        ·
          refine ⟨18012098363320725406729915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016131151094300542306553 18012098363320725406729915)
          ·
            refine ⟨27018147544981088110094873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012098363320725406729915 27018147544981088110094873)
            ·
              refine ⟨20263610658735816082571155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27018147544981088110094873 20263610658735816082571155)
              ·
                refine ⟨30395415988103724123856733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20263610658735816082571155 30395415988103724123856733)
                ·
                  refine ⟨11398280995538896546446275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30395415988103724123856733 11398280995538896546446275)
                  ·
                    refine ⟨17097421493308344819669413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11398280995538896546446275 17097421493308344819669413)
                    ·
                      refine ⟨3205766529995314653688015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17097421493308344819669413 3205766529995314653688015)
                      ·
                        rfl

theorem cell23_6243208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6243208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243208 prefixEnd_6243208 := by exact prefixLift 6243208
  have htrace : WordTrace (prefixWord ++ tailWord_6243208) baseStart_6243208 baseEnd_6243208 := by
    simpa [prefixWord, tailWord_6243208, baseEnd_6243208] using wordTrace_append hprefix tailTrace_6243208
  have hstable : (prefixWord ++ tailWord_6243208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243208).length < 2 ^ (prefixWord ++ tailWord_6243208).sum := by decide
  have hdescent : baseEnd_6243208 < baseStart_6243208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243231 : List Nat := [1, 1, 2, 5, 2, 2, 10]
def baseStart_6243231 : Nat := 118140960795 + 6243231 * 2 ^ 59
def prefixEnd_6243231 : Nat := 4983230072969 + 3 ^ 40 * 6243231 * 2
def baseEnd_6243231 : Nat := 39577510370992198317289

theorem tailTrace_6243231 : CollatzResearch.WordTrace tailWord_6243231 prefixEnd_6243231 39577510370992198317289 := by
  unfold tailWord_6243231
  simp only [CollatzResearch.WordTrace]
  refine ⟨227709341644847820810697547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151806227763231880540465031 227709341644847820810697547)
  ·
    refine ⟨341564012467271731216046321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227709341644847820810697547 341564012467271731216046321)
    ·
      refine ⟨256173009350453798412034741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341564012467271731216046321 256173009350453798412034741)
      ·
        refine ⟨24016219626605043601128257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256173009350453798412034741 24016219626605043601128257)
        ·
          refine ⟨18012164719953782700846193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016219626605043601128257 18012164719953782700846193)
          ·
            refine ⟨13509123539965337025634645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18012164719953782700846193 13509123539965337025634645)
            ·
              refine ⟨39577510370992198317289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13509123539965337025634645 39577510370992198317289)
              ·
                rfl

theorem cell23_6243231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 10].length) (baseStart_6243231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243231 prefixEnd_6243231 := by exact prefixLift 6243231
  have htrace : WordTrace (prefixWord ++ tailWord_6243231) baseStart_6243231 baseEnd_6243231 := by
    simpa [prefixWord, tailWord_6243231, baseEnd_6243231] using wordTrace_append hprefix tailTrace_6243231
  have hstable : (prefixWord ++ tailWord_6243231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243231).length < 2 ^ (prefixWord ++ tailWord_6243231).sum := by decide
  have hdescent : baseEnd_6243231 < baseStart_6243231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243252 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6243252 : Nat := 118140960795 + 6243252 * 2 ^ 59
def prefixEnd_6243252 : Nat := 4983230072969 + 3 ^ 40 * 6243252 * 2
def baseEnd_6243252 : Nat := 1068596374381370827179271

theorem tailTrace_6243252 : CollatzResearch.WordTrace tailWord_6243252 prefixEnd_6243252 1068596374381370827179271 := by
  unfold tailWord_6243252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113855053788885870698606005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151806738385181160931474673 113855053788885870698606005)
  ·
    refine ⟨10673911292708050377994313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113855053788885870698606005 10673911292708050377994313)
    ·
      refine ⟨8005433469531037783495735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10673911292708050377994313 8005433469531037783495735)
      ·
        refine ⟨12008150204296556675243603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005433469531037783495735 12008150204296556675243603)
        ·
          refine ⟨18012225306444835012865405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12008150204296556675243603 18012225306444835012865405)
          ·
            refine ⟨6754584489916813129824527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18012225306444835012865405 6754584489916813129824527)
            ·
              refine ⟨10131876734875219694736791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754584489916813129824527 10131876734875219694736791)
              ·
                refine ⟨15197815102312829542105187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10131876734875219694736791 15197815102312829542105187)
                ·
                  refine ⟨22796722653469244313157781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15197815102312829542105187 22796722653469244313157781)
                  ·
                    refine ⟨1068596374381370827179271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22796722653469244313157781 1068596374381370827179271)
                    ·
                      rfl

theorem cell23_6243252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6243252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243252 prefixEnd_6243252 := by exact prefixLift 6243252
  have htrace : WordTrace (prefixWord ++ tailWord_6243252) baseStart_6243252 baseEnd_6243252 := by
    simpa [prefixWord, tailWord_6243252, baseEnd_6243252] using wordTrace_append hprefix tailTrace_6243252
  have hstable : (prefixWord ++ tailWord_6243252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243252).length < 2 ^ (prefixWord ++ tailWord_6243252).sum := by decide
  have hdescent : baseEnd_6243252 < baseStart_6243252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243271 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6243271 : Nat := 118140960795 + 6243271 * 2 ^ 59
def prefixEnd_6243271 : Nat := 4983230072969 + 3 ^ 40 * 6243271 * 2
def baseEnd_6243271 : Nat := 3205798879276547907200225

theorem tailTrace_6243271 : CollatzResearch.WordTrace tailWord_6243271 prefixEnd_6243271 3205798879276547907200225 := by
  unfold tailWord_6243271
  simp only [CollatzResearch.WordTrace]
  refine ⟨227710800564702907642153667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151807200376468605094769111 227710800564702907642153667)
  ·
    refine ⟨341566200847054361463230501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227710800564702907642153667 341566200847054361463230501)
    ·
      refine ⟨64043662658822692774355719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341566200847054361463230501 64043662658822692774355719)
      ·
        refine ⟨96065493988234039161533579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64043662658822692774355719 96065493988234039161533579)
        ·
          refine ⟨144098240982351058742300369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96065493988234039161533579 144098240982351058742300369)
          ·
            refine ⟨108073680736763294056725277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144098240982351058742300369 108073680736763294056725277)
            ·
              refine ⟨40527630276286235271271979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108073680736763294056725277 40527630276286235271271979)
              ·
                refine ⟨60791445414429352906907969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40527630276286235271271979 60791445414429352906907969)
                ·
                  refine ⟨45593584060822014680180977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60791445414429352906907969 45593584060822014680180977)
                  ·
                    refine ⟨34195188045616511010135733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45593584060822014680180977 34195188045616511010135733)
                    ·
                      refine ⟨3205798879276547907200225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34195188045616511010135733 3205798879276547907200225)
                      ·
                        rfl

theorem cell23_6243271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6243271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243271 prefixEnd_6243271 := by exact prefixLift 6243271
  have htrace : WordTrace (prefixWord ++ tailWord_6243271) baseStart_6243271 baseEnd_6243271 := by
    simpa [prefixWord, tailWord_6243271, baseEnd_6243271] using wordTrace_append hprefix tailTrace_6243271
  have hstable : (prefixWord ++ tailWord_6243271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243271).length < 2 ^ (prefixWord ++ tailWord_6243271).sum := by decide
  have hdescent : baseEnd_6243271 < baseStart_6243271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243321 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 9]
def baseStart_6243321 : Nat := 118140960795 + 6243321 * 2 ^ 59
def prefixEnd_6243321 : Nat := 4983230072969 + 3 ^ 40 * 6243321 * 2
def baseEnd_6243321 : Nat := 356202728145474745730555

theorem tailTrace_6243321 : CollatzResearch.WordTrace tailWord_6243321 prefixEnd_6243321 356202728145474745730555 := by
  unfold tailWord_6243321
  simp only [CollatzResearch.WordTrace]
  refine ⟨227712624214521766181473817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151808416143014510787649211 227712624214521766181473817)
  ·
    refine ⟨170784468160891324636105363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227712624214521766181473817 170784468160891324636105363)
    ·
      refine ⟨256176702241336986954158045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170784468160891324636105363 256176702241336986954158045)
      ·
        refine ⟨96066263340501370107809267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256176702241336986954158045 96066263340501370107809267)
        ·
          refine ⟨144099395010752055161713901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96066263340501370107809267 144099395010752055161713901)
          ·
            refine ⟨54037273129032020685642713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144099395010752055161713901 54037273129032020685642713)
            ·
              refine ⟨40527954846774015514232035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54037273129032020685642713 40527954846774015514232035)
              ·
                refine ⟨60791932270161023271348053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40527954846774015514232035 60791932270161023271348053)
                ·
                  refine ⟨356202728145474745730555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60791932270161023271348053 356202728145474745730555)
                  ·
                    rfl

theorem cell23_6243321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_6243321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243321 prefixEnd_6243321 := by exact prefixLift 6243321
  have htrace : WordTrace (prefixWord ++ tailWord_6243321) baseStart_6243321 baseEnd_6243321 := by
    simpa [prefixWord, tailWord_6243321, baseEnd_6243321] using wordTrace_append hprefix tailTrace_6243321
  have hstable : (prefixWord ++ tailWord_6243321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243321).length < 2 ^ (prefixWord ++ tailWord_6243321).sum := by decide
  have hdescent : baseEnd_6243321 < baseStart_6243321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243349 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_6243349 : Nat := 118140960795 + 6243349 * 2 ^ 59
def prefixEnd_6243349 : Nat := 4983230072969 + 3 ^ 40 * 6243349 * 2
def baseEnd_6243349 : Nat := 3205838930767598602024867

theorem tailTrace_6243349 : CollatzResearch.WordTrace tailWord_6243349 prefixEnd_6243349 3205838930767598602024867 := by
  unfold tailWord_6243349
  simp only [CollatzResearch.WordTrace]
  refine ⟨227713645458420326963493101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151809096972280217975662067 227713645458420326963493101)
  ·
    refine ⟨85392617046907622611309913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227713645458420326963493101 85392617046907622611309913)
    ·
      refine ⟨64044462785180716958482435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85392617046907622611309913 64044462785180716958482435)
      ·
        refine ⟨96066694177771075437723653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64044462785180716958482435 96066694177771075437723653)
        ·
          refine ⟨18012505158332076644573185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96066694177771075437723653 18012505158332076644573185)
          ·
            refine ⟨13509378868749057483429889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18012505158332076644573185 13509378868749057483429889)
            ·
              refine ⟨10132034151561793112572417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13509378868749057483429889 10132034151561793112572417)
              ·
                refine ⟨7599025613671344834429313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132034151561793112572417 7599025613671344834429313)
                ·
                  refine ⟨5699269210253508625821985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599025613671344834429313 5699269210253508625821985)
                  ·
                    refine ⟨4274451907690131469366489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699269210253508625821985 4274451907690131469366489)
                    ·
                      refine ⟨3205838930767598602024867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274451907690131469366489 3205838930767598602024867)
                      ·
                        rfl

theorem cell23_6243349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_6243349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243349 prefixEnd_6243349 := by exact prefixLift 6243349
  have htrace : WordTrace (prefixWord ++ tailWord_6243349) baseStart_6243349 baseEnd_6243349 := by
    simpa [prefixWord, tailWord_6243349, baseEnd_6243349] using wordTrace_append hprefix tailTrace_6243349
  have hstable : (prefixWord ++ tailWord_6243349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243349).length < 2 ^ (prefixWord ++ tailWord_6243349).sum := by decide
  have hdescent : baseEnd_6243349 < baseStart_6243349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243385 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_6243385 : Nat := 118140960795 + 6243385 * 2 ^ 59
def prefixEnd_6243385 : Nat := 4983230072969 + 3 ^ 40 * 6243385 * 2
def baseEnd_6243385 : Nat := 1068619138690386820391567

theorem tailTrace_6243385 : CollatzResearch.WordTrace tailWord_6243385 prefixEnd_6243385 1068619138690386820391567 := by
  unfold tailWord_6243385
  simp only [CollatzResearch.WordTrace]
  refine ⟨227714958486289905111803609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151809972324193270074535739 227714958486289905111803609)
  ·
    refine ⟨170786218864717428833852707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227714958486289905111803609 170786218864717428833852707)
    ·
      refine ⟨256179328297076143250779061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170786218864717428833852707 256179328297076143250779061)
      ·
        refine ⟨24016812027850888429760537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256179328297076143250779061 24016812027850888429760537)
        ·
          refine ⟨18012609020888166322320403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016812027850888429760537 18012609020888166322320403)
          ·
            refine ⟨27018913531332249483480605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012609020888166322320403 27018913531332249483480605)
            ·
              refine ⟨10132092574249593556305227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27018913531332249483480605 10132092574249593556305227)
              ·
                refine ⟨15198138861374390334457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10132092574249593556305227 15198138861374390334457841)
                ·
                  refine ⟨11398604146030792750843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15198138861374390334457841 11398604146030792750843381)
                  ·
                    refine ⟨1068619138690386820391567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11398604146030792750843381 1068619138690386820391567)
                    ·
                      rfl

theorem cell23_6243385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_6243385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243385 prefixEnd_6243385 := by exact prefixLift 6243385
  have htrace : WordTrace (prefixWord ++ tailWord_6243385) baseStart_6243385 baseEnd_6243385 := by
    simpa [prefixWord, tailWord_6243385, baseEnd_6243385] using wordTrace_append hprefix tailTrace_6243385
  have hstable : (prefixWord ++ tailWord_6243385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243385).length < 2 ^ (prefixWord ++ tailWord_6243385).sum := by decide
  have hdescent : baseEnd_6243385 < baseStart_6243385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243492 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_6243492 : Nat := 118140960795 + 6243492 * 2 ^ 59
def prefixEnd_6243492 : Nat := 4983230072969 + 3 ^ 40 * 6243492 * 2
def baseEnd_6243492 : Nat := 1068637452833730514178903

theorem tailTrace_6243492 : CollatzResearch.WordTrace tailWord_6243492 prefixEnd_6243492 1068637452833730514178903 := by
  unfold tailWord_6243492
  simp only [CollatzResearch.WordTrace]
  refine ⟨113859430548451131192974365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151812574064601508257299153 113859430548451131192974365)
  ·
    refine ⟨42697286455669174197365387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113859430548451131192974365 42697286455669174197365387)
    ·
      refine ⟨64045929683503761296048081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42697286455669174197365387 64045929683503761296048081)
      ·
        refine ⟨48034447262627820972036061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64045929683503761296048081 48034447262627820972036061)
        ·
          refine ⟨18012917723485432864513523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48034447262627820972036061 18012917723485432864513523)
          ·
            refine ⟨27019376585228149296770285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012917723485432864513523 27019376585228149296770285)
            ·
              refine ⟨10132266219460555986288857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27019376585228149296770285 10132266219460555986288857)
              ·
                refine ⟨7599199664595416989716643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132266219460555986288857 7599199664595416989716643)
                ·
                  refine ⟨11398799496893125484574965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599199664595416989716643 11398799496893125484574965)
                  ·
                    refine ⟨1068637452833730514178903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11398799496893125484574965 1068637452833730514178903)
                    ·
                      rfl

theorem cell23_6243492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_6243492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243492 prefixEnd_6243492 := by exact prefixLift 6243492
  have htrace : WordTrace (prefixWord ++ tailWord_6243492) baseStart_6243492 baseEnd_6243492 := by
    simpa [prefixWord, tailWord_6243492, baseEnd_6243492] using wordTrace_append hprefix tailTrace_6243492
  have hstable : (prefixWord ++ tailWord_6243492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243492).length < 2 ^ (prefixWord ++ tailWord_6243492).sum := by decide
  have hdescent : baseEnd_6243492 < baseStart_6243492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243505 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_6243505 : Nat := 118140960795 + 6243505 * 2 ^ 59
def prefixEnd_6243505 : Nat := 4983230072969 + 3 ^ 40 * 6243505 * 2
def baseEnd_6243505 : Nat := 1068639677916566663891383

theorem tailTrace_6243505 : CollatzResearch.WordTrace tailWord_6243505 prefixEnd_6243505 1068639677916566663891383 := by
  unfold tailWord_6243505
  simp only [CollatzResearch.WordTrace]
  refine ⟨227719335245855165606171969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151812890163903443737447979 227719335245855165606171969)
  ·
    refine ⟨170789501434391374204628977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227719335245855165606171969 170789501434391374204628977)
    ·
      refine ⟨128092126075793530653471733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170789501434391374204628977 128092126075793530653471733)
      ·
        refine ⟨12008636819605643498762975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128092126075793530653471733 12008636819605643498762975)
        ·
          refine ⟨18012955229408465248144463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12008636819605643498762975 18012955229408465248144463)
          ·
            refine ⟨27019432844112697872216695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012955229408465248144463 27019432844112697872216695)
            ·
              refine ⟨40529149266169046808325043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27019432844112697872216695 40529149266169046808325043)
              ·
                refine ⟨60793723899253570212487565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40529149266169046808325043 60793723899253570212487565)
                ·
                  refine ⟨22797646462220088829682837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60793723899253570212487565 22797646462220088829682837)
                  ·
                    refine ⟨1068639677916566663891383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22797646462220088829682837 1068639677916566663891383)
                    ·
                      rfl

theorem cell23_6243505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_6243505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243505 prefixEnd_6243505 := by exact prefixLift 6243505
  have htrace : WordTrace (prefixWord ++ tailWord_6243505) baseStart_6243505 baseEnd_6243505 := by
    simpa [prefixWord, tailWord_6243505, baseEnd_6243505] using wordTrace_append hprefix tailTrace_6243505
  have hstable : (prefixWord ++ tailWord_6243505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243505).length < 2 ^ (prefixWord ++ tailWord_6243505).sum := by decide
  have hdescent : baseEnd_6243505 < baseStart_6243505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243512 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_6243512 : Nat := 118140960795 + 6243512 * 2 ^ 59
def prefixEnd_6243512 : Nat := 4983230072969 + 3 ^ 40 * 6243512 * 2
def baseEnd_6243512 : Nat := 3205922628114281464286617

theorem tailTrace_6243512 : CollatzResearch.WordTrace tailWord_6243512 prefixEnd_6243512 3205922628114281464286617 := by
  unfold tailWord_6243512
  simp only [CollatzResearch.WordTrace]
  refine ⟨113859795278414902900838395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151813060371219870534451193 113859795278414902900838395)
  ·
    refine ⟨170789692917622354351257593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113859795278414902900838395 170789692917622354351257593)
    ·
      refine ⟨128092269688216765763443195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170789692917622354351257593 128092269688216765763443195)
      ·
        refine ⟨192138404532325148645164793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128092269688216765763443195 192138404532325148645164793)
        ·
          refine ⟨144103803399243861483873595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192138404532325148645164793 144103803399243861483873595)
          ·
            refine ⟨216155705098865792225810393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144103803399243861483873595 216155705098865792225810393)
            ·
              refine ⟨162116778824149344169357795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216155705098865792225810393 162116778824149344169357795)
              ·
                refine ⟨243175168236224016254036693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162116778824149344169357795 243175168236224016254036693)
                ·
                  refine ⟨5699418005536500380953985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243175168236224016254036693 5699418005536500380953985)
                  ·
                    refine ⟨4274563504152375285715489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699418005536500380953985 4274563504152375285715489)
                    ·
                      refine ⟨3205922628114281464286617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274563504152375285715489 3205922628114281464286617)
                      ·
                        rfl

theorem cell23_6243512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_6243512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243512 prefixEnd_6243512 := by exact prefixLift 6243512
  have htrace : WordTrace (prefixWord ++ tailWord_6243512) baseStart_6243512 baseEnd_6243512 := by
    simpa [prefixWord, tailWord_6243512, baseEnd_6243512] using wordTrace_append hprefix tailTrace_6243512
  have hstable : (prefixWord ++ tailWord_6243512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243512).length < 2 ^ (prefixWord ++ tailWord_6243512).sum := by decide
  have hdescent : baseEnd_6243512 < baseStart_6243512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243562 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_6243562 : Nat := 118140960795 + 6243562 * 2 ^ 59
def prefixEnd_6243562 : Nat := 4983230072969 + 3 ^ 40 * 6243562 * 2
def baseEnd_6243562 : Nat := 3205948302147006268661387

theorem tailTrace_6243562 : CollatzResearch.WordTrace tailWord_6243562 prefixEnd_6243562 3205948302147006268661387 := by
  unfold tailWord_6243562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56930353551662166085249235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151814276137765776227331293 56930353551662166085249235)
  ·
    refine ⟨85395530327493249127873853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56930353551662166085249235 85395530327493249127873853)
    ·
      refine ⟨32023323872809968422952695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85395530327493249127873853 32023323872809968422952695)
      ·
        refine ⟨48034985809214952634429043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32023323872809968422952695 48034985809214952634429043)
        ·
          refine ⟨72052478713822428951643565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48034985809214952634429043 72052478713822428951643565)
          ·
            refine ⟨27019679517683410856866337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72052478713822428951643565 27019679517683410856866337)
            ·
              refine ⟨20264759638262558142649753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27019679517683410856866337 20264759638262558142649753)
              ·
                refine ⟨15198569728696918606987315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20264759638262558142649753 15198569728696918606987315)
                ·
                  refine ⟨22797854593045377910480973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15198569728696918606987315 22797854593045377910480973)
                  ·
                    refine ⟨8549195472392016716430365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22797854593045377910480973 8549195472392016716430365)
                    ·
                      refine ⟨3205948302147006268661387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549195472392016716430365 3205948302147006268661387)
                      ·
                        rfl

theorem cell23_6243562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_6243562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243562 prefixEnd_6243562 := by exact prefixLift 6243562
  have htrace : WordTrace (prefixWord ++ tailWord_6243562) baseStart_6243562 baseEnd_6243562 := by
    simpa [prefixWord, tailWord_6243562, baseEnd_6243562] using wordTrace_append hprefix tailTrace_6243562
  have hstable : (prefixWord ++ tailWord_6243562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243562).length < 2 ^ (prefixWord ++ tailWord_6243562).sum := by decide
  have hdescent : baseEnd_6243562 < baseStart_6243562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243595 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 6]
def baseStart_6243595 : Nat := 118140960795 + 6243595 * 2 ^ 59
def prefixEnd_6243595 : Nat := 4983230072969 + 3 ^ 40 * 6243595 * 2
def baseEnd_6243595 : Nat := 1068655082336201546516245

theorem tailTrace_6243595 : CollatzResearch.WordTrace tailWord_6243595 prefixEnd_6243595 1068655082336201546516245 := by
  unfold tailWord_6243595
  simp only [CollatzResearch.WordTrace]
  refine ⟨227722617815529110976948239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151815078543686073984632159 227722617815529110976948239)
  ·
    refine ⟨341583926723293666465422359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227722617815529110976948239 341583926723293666465422359)
    ·
      refine ⟨512375890084940499698133539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341583926723293666465422359 512375890084940499698133539)
      ·
        refine ⟨768563835127410749547200309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512375890084940499698133539 768563835127410749547200309)
        ·
          refine ⟨72052859543194757770050029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 768563835127410749547200309 72052859543194757770050029)
          ·
            refine ⟨27019822328698034163768761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72052859543194757770050029 27019822328698034163768761)
            ·
              refine ⟨20264866746523525622826571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27019822328698034163768761 20264866746523525622826571)
              ·
                refine ⟨30397300119785288434239857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20264866746523525622826571 30397300119785288434239857)
                ·
                  refine ⟨22797975089838966325679893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30397300119785288434239857 22797975089838966325679893)
                  ·
                    refine ⟨1068655082336201546516245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22797975089838966325679893 1068655082336201546516245)
                    ·
                      rfl

theorem cell23_6243595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_6243595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243595 prefixEnd_6243595 := by exact prefixLift 6243595
  have htrace : WordTrace (prefixWord ++ tailWord_6243595) baseStart_6243595 baseEnd_6243595 := by
    simpa [prefixWord, tailWord_6243595, baseEnd_6243595] using wordTrace_append hprefix tailTrace_6243595
  have hstable : (prefixWord ++ tailWord_6243595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243595).length < 2 ^ (prefixWord ++ tailWord_6243595).sum := by decide
  have hdescent : baseEnd_6243595 < baseStart_6243595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243596 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_6243596 : Nat := 118140960795 + 6243596 * 2 ^ 59
def prefixEnd_6243596 : Nat := 4983230072969 + 3 ^ 40 * 6243596 * 2
def baseEnd_6243596 : Nat := 3205965760489259135636231

theorem tailTrace_6243596 : CollatzResearch.WordTrace tailWord_6243596 prefixEnd_6243596 3205965760489259135636231 := by
  unfold tailWord_6243596
  simp only [CollatzResearch.WordTrace]
  refine ⟨113861327144262744073867321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151815102859016992098489761 113861327144262744073867321)
  ·
    refine ⟨85395995358197058055400491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113861327144262744073867321 85395995358197058055400491)
    ·
      refine ⟨128093993037295587083100737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85395995358197058055400491 128093993037295587083100737)
      ·
        refine ⟨96070494777971690312325553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128093993037295587083100737 96070494777971690312325553)
        ·
          refine ⟨72052871083478767734244165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96070494777971690312325553 72052871083478767734244165)
          ·
            refine ⟨13509913328152268950170781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72052871083478767734244165 13509913328152268950170781)
            ·
              refine ⟨5066217498057100856314043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13509913328152268950170781 5066217498057100856314043)
              ·
                refine ⟨7599326247085651284471065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066217498057100856314043 7599326247085651284471065)
                ·
                  refine ⟨5699494685314238463353299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599326247085651284471065 5699494685314238463353299)
                  ·
                    refine ⟨8549242027971357695029949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5699494685314238463353299 8549242027971357695029949)
                    ·
                      refine ⟨3205965760489259135636231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549242027971357695029949 3205965760489259135636231)
                      ·
                        rfl

theorem cell23_6243596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_6243596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243596 prefixEnd_6243596 := by exact prefixLift 6243596
  have htrace : WordTrace (prefixWord ++ tailWord_6243596) baseStart_6243596 baseEnd_6243596 := by
    simpa [prefixWord, tailWord_6243596, baseEnd_6243596] using wordTrace_append hprefix tailTrace_6243596
  have hstable : (prefixWord ++ tailWord_6243596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243596).length < 2 ^ (prefixWord ++ tailWord_6243596).sum := by decide
  have hdescent : baseEnd_6243596 < baseStart_6243596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243605 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6243605 : Nat := 118140960795 + 6243605 * 2 ^ 59
def prefixEnd_6243605 : Nat := 4983230072969 + 3 ^ 40 * 6243605 * 2
def baseEnd_6243605 : Nat := 3205970381815149600423689

theorem tailTrace_6243605 : CollatzResearch.WordTrace tailWord_6243605 prefixEnd_6243605 3205970381815149600423689 := by
  unfold tailWord_6243605
  simp only [CollatzResearch.WordTrace]
  refine ⟨227722982545492882684812269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151815321696995255123208179 227722982545492882684812269)
  ·
    refine ⟨85396118454559831006804601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227722982545492882684812269 85396118454559831006804601)
    ·
      refine ⟨64047088840919873255103451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85396118454559831006804601 64047088840919873255103451)
      ·
        refine ⟨96070633261379809882655177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64047088840919873255103451 96070633261379809882655177)
        ·
          refine ⟨72052974946034857411991383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96070633261379809882655177 72052974946034857411991383)
          ·
            refine ⟨108079462419052286117987075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72052974946034857411991383 108079462419052286117987075)
            ·
              refine ⟨162119193628578429176980613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108079462419052286117987075 162119193628578429176980613)
              ·
                refine ⟨30397348805358455470683865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162119193628578429176980613 30397348805358455470683865)
                ·
                  refine ⟨22798011604018841603012899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30397348805358455470683865 22798011604018841603012899)
                  ·
                    refine ⟨34197017406028262404519349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22798011604018841603012899 34197017406028262404519349)
                    ·
                      refine ⟨3205970381815149600423689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34197017406028262404519349 3205970381815149600423689)
                      ·
                        rfl

theorem cell23_6243605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6243605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243605 prefixEnd_6243605 := by exact prefixLift 6243605
  have htrace : WordTrace (prefixWord ++ tailWord_6243605) baseStart_6243605 baseEnd_6243605 := by
    simpa [prefixWord, tailWord_6243605, baseEnd_6243605] using wordTrace_append hprefix tailTrace_6243605
  have hstable : (prefixWord ++ tailWord_6243605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243605).length < 2 ^ (prefixWord ++ tailWord_6243605).sum := by decide
  have hdescent : baseEnd_6243605 < baseStart_6243605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243614 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6243614 : Nat := 118140960795 + 6243614 * 2 ^ 59
def prefixEnd_6243614 : Nat := 4983230072969 + 3 ^ 40 * 6243614 * 2
def baseEnd_6243614 : Nat := 3205975003141040065211149

theorem tailTrace_6243614 : CollatzResearch.WordTrace tailWord_6243614 prefixEnd_6243614 3205975003141040065211149 := by
  unfold tailWord_6243614
  simp only [CollatzResearch.WordTrace]
  refine ⟨28465413850307534652736237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151815540534973518147926597 28465413850307534652736237)
  ·
    refine ⟨10674530193865325494776089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28465413850307534652736237 10674530193865325494776089)
    ·
      refine ⟨8005897645398994121082067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10674530193865325494776089 8005897645398994121082067)
      ·
        refine ⟨12008846468098491181623101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005897645398994121082067 12008846468098491181623101)
        ·
          refine ⟨4503317425536934193108663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12008846468098491181623101 4503317425536934193108663)
          ·
            refine ⟨6754976138305401289662995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503317425536934193108663 6754976138305401289662995)
            ·
              refine ⟨10132464207458101934494493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754976138305401289662995 10132464207458101934494493)
              ·
                refine ⟨3799674077796788225435435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10132464207458101934494493 3799674077796788225435435)
                ·
                  refine ⟨5699511116695182338153153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799674077796788225435435 5699511116695182338153153)
                  ·
                    refine ⟨4274633337521386753614865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699511116695182338153153 4274633337521386753614865)
                    ·
                      refine ⟨3205975003141040065211149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274633337521386753614865 3205975003141040065211149)
                      ·
                        rfl

theorem cell23_6243614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6243614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243614 prefixEnd_6243614 := by exact prefixLift 6243614
  have htrace : WordTrace (prefixWord ++ tailWord_6243614) baseStart_6243614 baseEnd_6243614 := by
    simpa [prefixWord, tailWord_6243614, baseEnd_6243614] using wordTrace_append hprefix tailTrace_6243614
  have hstable : (prefixWord ++ tailWord_6243614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243614).length < 2 ^ (prefixWord ++ tailWord_6243614).sum := by decide
  have hdescent : baseEnd_6243614 < baseStart_6243614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243619 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 4, 2, 2]
def baseStart_6243619 : Nat := 118140960795 + 6243619 * 2 ^ 59
def prefixEnd_6243619 : Nat := 4983230072969 + 3 ^ 40 * 6243619 * 2
def baseEnd_6243619 : Nat := 3205977570544312545648625

theorem tailTrace_6243619 : CollatzResearch.WordTrace tailWord_6243619 prefixEnd_6243619 3205977570544312545648625 := by
  unfold tailWord_6243619
  simp only [CollatzResearch.WordTrace]
  refine ⟨227723493167442163075821911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151815662111628108717214607 227723493167442163075821911)
  ·
    refine ⟨341585239751163244613732867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227723493167442163075821911 341585239751163244613732867)
    ·
      refine ⟨512377859626744866920599301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341585239751163244613732867 512377859626744866920599301)
      ·
        refine ⟨96070848680014662547612369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512377859626744866920599301 96070848680014662547612369)
        ·
          refine ⟨72053136510010996910709277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96070848680014662547612369 72053136510010996910709277)
          ·
            refine ⟨27019926191254123841515979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72053136510010996910709277 27019926191254123841515979)
            ·
              refine ⟨40529889286881185762273969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27019926191254123841515979 40529889286881185762273969)
              ·
                refine ⟨30397416965160889321705477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40529889286881185762273969 30397416965160889321705477)
                ·
                  refine ⟨5699515680967666747819777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30397416965160889321705477 5699515680967666747819777)
                  ·
                    refine ⟨4274636760725750060864833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699515680967666747819777 4274636760725750060864833)
                    ·
                      refine ⟨3205977570544312545648625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274636760725750060864833 3205977570544312545648625)
                      ·
                        rfl

theorem cell23_6243619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_6243619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243619 prefixEnd_6243619 := by exact prefixLift 6243619
  have htrace : WordTrace (prefixWord ++ tailWord_6243619) baseStart_6243619 baseEnd_6243619 := by
    simpa [prefixWord, tailWord_6243619, baseEnd_6243619] using wordTrace_append hprefix tailTrace_6243619
  have hstable : (prefixWord ++ tailWord_6243619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243619).length < 2 ^ (prefixWord ++ tailWord_6243619).sum := by decide
  have hdescent : baseEnd_6243619 < baseStart_6243619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243636 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6243636 : Nat := 118140960795 + 6243636 * 2 ^ 59
def prefixEnd_6243636 : Nat := 4983230072969 + 3 ^ 40 * 6243636 * 2
def baseEnd_6243636 : Nat := 3205986299715438979136047

theorem tailTrace_6243636 : CollatzResearch.WordTrace tailWord_6243636 prefixEnd_6243636 3205986299715438979136047 := by
  unfold tailWord_6243636
  simp only [CollatzResearch.WordTrace]
  refine ⟨113862056604190287489595381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151816075472253716652793841 113862056604190287489595381)
  ·
    refine ⟨10674567806642839452149567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113862056604190287489595381 10674567806642839452149567)
    ·
      refine ⟨16011851709964259178224351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10674567806642839452149567 16011851709964259178224351)
      ·
        refine ⟨24017777564946388767336527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16011851709964259178224351 24017777564946388767336527)
        ·
          refine ⟨36026666347419583151004791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24017777564946388767336527 36026666347419583151004791)
          ·
            refine ⟨54039999521129374726507187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36026666347419583151004791 54039999521129374726507187)
            ·
              refine ⟨81059999281694062089760781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54039999521129374726507187 81059999281694062089760781)
              ·
                refine ⟨30397499730635273283660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81059999281694062089760781 30397499730635273283660293)
                ·
                  refine ⟨5699531199494113740686305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30397499730635273283660293 5699531199494113740686305)
                  ·
                    refine ⟨4274648399620585305514729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699531199494113740686305 4274648399620585305514729)
                    ·
                      refine ⟨3205986299715438979136047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274648399620585305514729 3205986299715438979136047)
                      ·
                        rfl

theorem cell23_6243636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6243636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243636 prefixEnd_6243636 := by exact prefixLift 6243636
  have htrace : WordTrace (prefixWord ++ tailWord_6243636) baseStart_6243636 baseEnd_6243636 := by
    simpa [prefixWord, tailWord_6243636, baseEnd_6243636] using wordTrace_append hprefix tailTrace_6243636
  have hstable : (prefixWord ++ tailWord_6243636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243636).length < 2 ^ (prefixWord ++ tailWord_6243636).sum := by decide
  have hdescent : baseEnd_6243636 < baseStart_6243636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243665 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_6243665 : Nat := 118140960795 + 6243665 * 2 ^ 59
def prefixEnd_6243665 : Nat := 4983230072969 + 3 ^ 40 * 6243665 * 2
def baseEnd_6243665 : Nat := 3206001190654419365673413

theorem tailTrace_6243665 : CollatzResearch.WordTrace tailWord_6243665 prefixEnd_6243665 3206001190654419365673413 := by
  unfold tailWord_6243665
  simp only [CollatzResearch.WordTrace]
  refine ⟨227725170925275512931996449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151816780616850341954664299 227725170925275512931996449)
  ·
    refine ⟨170793878193956634698997337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227725170925275512931996449 170793878193956634698997337)
    ·
      refine ⟨128095408645467476024248003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170793878193956634698997337 128095408645467476024248003)
      ·
        refine ⟨192143112968201214036372005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128095408645467476024248003 192143112968201214036372005)
        ·
          refine ⟨36026833681537727631819751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192143112968201214036372005 36026833681537727631819751)
          ·
            refine ⟨54040250522306591447729627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36026833681537727631819751 54040250522306591447729627)
            ·
              refine ⟨81060375783459887171594441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54040250522306591447729627 81060375783459887171594441)
              ·
                refine ⟨60795281837594915378695831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81060375783459887171594441 60795281837594915378695831)
                ·
                  refine ⟨91192922756392373068043747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60795281837594915378695831 91192922756392373068043747)
                  ·
                    refine ⟨136789384134588559602065621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91192922756392373068043747 136789384134588559602065621)
                    ·
                      refine ⟨3206001190654419365673413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136789384134588559602065621 3206001190654419365673413)
                      ·
                        rfl

theorem cell23_6243665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_6243665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243665 prefixEnd_6243665 := by exact prefixLift 6243665
  have htrace : WordTrace (prefixWord ++ tailWord_6243665) baseStart_6243665 baseEnd_6243665 := by
    simpa [prefixWord, tailWord_6243665, baseEnd_6243665] using wordTrace_append hprefix tailTrace_6243665
  have hstable : (prefixWord ++ tailWord_6243665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243665).length < 2 ^ (prefixWord ++ tailWord_6243665).sum := by decide
  have hdescent : baseEnd_6243665 < baseStart_6243665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243672 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_6243672 : Nat := 118140960795 + 6243672 * 2 ^ 59
def prefixEnd_6243672 : Nat := 4983230072969 + 3 ^ 40 * 6243672 * 2
def baseEnd_6243672 : Nat := 1068668261673000279428627

theorem tailTrace_6243672 : CollatzResearch.WordTrace tailWord_6243672 prefixEnd_6243672 1068668261673000279428627 := by
  unfold tailWord_6243672
  simp only [CollatzResearch.WordTrace]
  refine ⟨113862713118125076563750635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151816950824166768751667513 113862713118125076563750635)
  ·
    refine ⟨170794069677187614845625953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113862713118125076563750635 170794069677187614845625953)
    ·
      refine ⟨128095552257890711134219465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170794069677187614845625953 128095552257890711134219465)
      ·
        refine ⟨96071664193418033350664599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128095552257890711134219465 96071664193418033350664599)
        ·
          refine ⟨144107496290127050025996899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96071664193418033350664599 144107496290127050025996899)
          ·
            refine ⟨216161244435190575038995349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144107496290127050025996899 216161244435190575038995349)
            ·
              refine ⟨10132558332899558204952907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216161244435190575038995349 10132558332899558204952907)
              ·
                refine ⟨15198837499349337307429361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10132558332899558204952907 15198837499349337307429361)
                ·
                  refine ⟨11399128124512002980572021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15198837499349337307429361 11399128124512002980572021)
                  ·
                    refine ⟨1068668261673000279428627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11399128124512002980572021 1068668261673000279428627)
                    ·
                      rfl

theorem cell23_6243672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_6243672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243672 prefixEnd_6243672 := by exact prefixLift 6243672
  have htrace : WordTrace (prefixWord ++ tailWord_6243672) baseStart_6243672 baseEnd_6243672 := by
    simpa [prefixWord, tailWord_6243672, baseEnd_6243672] using wordTrace_append hprefix tailTrace_6243672
  have hstable : (prefixWord ++ tailWord_6243672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243672).length < 2 ^ (prefixWord ++ tailWord_6243672).sum := by decide
  have hdescent : baseEnd_6243672 < baseStart_6243672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243682 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6243682 : Nat := 118140960795 + 6243682 * 2 ^ 59
def prefixEnd_6243682 : Nat := 4983230072969 + 3 ^ 40 * 6243682 * 2
def baseEnd_6243682 : Nat := 3206009919825545799160835

theorem tailTrace_6243682 : CollatzResearch.WordTrace tailWord_6243682 prefixEnd_6243682 3206009919825545799160835 := by
  unfold tailWord_6243682
  simp only [CollatzResearch.WordTrace]
  refine ⟨56931447741553481208841325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151817193977475949890243533 56931447741553481208841325)
  ·
    refine ⟨21349292903082555453315497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56931447741553481208841325 21349292903082555453315497)
    ·
      refine ⟨16011969677311916589986623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21349292903082555453315497 16011969677311916589986623)
      ·
        refine ⟨24017954515967874884979935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16011969677311916589986623 24017954515967874884979935)
        ·
          refine ⟨36026931773951812327469903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24017954515967874884979935 36026931773951812327469903)
          ·
            refine ⟨54040397660927718491204855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36026931773951812327469903 54040397660927718491204855)
            ·
              refine ⟨81060596491391577736807283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54040397660927718491204855 81060596491391577736807283)
              ·
                refine ⟨121590894737087366605210925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81060596491391577736807283 121590894737087366605210925)
                ·
                  refine ⟨45596585526407762476954097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121590894737087366605210925 45596585526407762476954097)
                  ·
                    refine ⟨34197439144805821857715573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45596585526407762476954097 34197439144805821857715573)
                    ·
                      refine ⟨3206009919825545799160835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34197439144805821857715573 3206009919825545799160835)
                      ·
                        rfl

theorem cell23_6243682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6243682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243682 prefixEnd_6243682 := by exact prefixLift 6243682
  have htrace : WordTrace (prefixWord ++ tailWord_6243682) baseStart_6243682 baseEnd_6243682 := by
    simpa [prefixWord, tailWord_6243682, baseEnd_6243682] using wordTrace_append hprefix tailTrace_6243682
  have hstable : (prefixWord ++ tailWord_6243682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243682).length < 2 ^ (prefixWord ++ tailWord_6243682).sum := by decide
  have hdescent : baseEnd_6243682 < baseStart_6243682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243695 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_6243695 : Nat := 118140960795 + 6243695 * 2 ^ 59
def prefixEnd_6243695 : Nat := 4983230072969 + 3 ^ 40 * 6243695 * 2
def baseEnd_6243695 : Nat := 3206016595074054248298275

theorem tailTrace_6243695 : CollatzResearch.WordTrace tailWord_6243695 prefixEnd_6243695 3206016595074054248298275 := by
  unfold tailWord_6243695
  simp only [CollatzResearch.WordTrace]
  refine ⟨227726265115166828055588539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151817510076777885370392359 227726265115166828055588539)
  ·
    refine ⟨341589397672750242083382809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227726265115166828055588539 341589397672750242083382809)
    ·
      refine ⟨256192048254562681562537107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341589397672750242083382809 256192048254562681562537107)
      ·
        refine ⟨384288072381844022343805661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256192048254562681562537107 384288072381844022343805661)
        ·
          refine ⟨144108027143191508378927123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384288072381844022343805661 144108027143191508378927123)
          ·
            refine ⟨216162040714787262568390685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144108027143191508378927123 216162040714787262568390685)
            ·
              refine ⟨81060765268045223463146507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216162040714787262568390685 81060765268045223463146507)
              ·
                refine ⟨121591147902067835194719761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81060765268045223463146507 121591147902067835194719761)
                ·
                  refine ⟨91193360926550876396039821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121591147902067835194719761 91193360926550876396039821)
                  ·
                    refine ⟨34197510347456578648514933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91193360926550876396039821 34197510347456578648514933)
                    ·
                      refine ⟨3206016595074054248298275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34197510347456578648514933 3206016595074054248298275)
                      ·
                        rfl

theorem cell23_6243695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_6243695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243695 prefixEnd_6243695 := by exact prefixLift 6243695
  have htrace : WordTrace (prefixWord ++ tailWord_6243695) baseStart_6243695 baseEnd_6243695 := by
    simpa [prefixWord, tailWord_6243695, baseEnd_6243695] using wordTrace_append hprefix tailTrace_6243695
  have hstable : (prefixWord ++ tailWord_6243695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243695).length < 2 ^ (prefixWord ++ tailWord_6243695).sum := by decide
  have hdescent : baseEnd_6243695 < baseStart_6243695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243709 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_6243709 : Nat := 118140960795 + 6243709 * 2 ^ 59
def prefixEnd_6243709 : Nat := 4983230072969 + 3 ^ 40 * 6243709 * 2
def baseEnd_6243709 : Nat := 3206023783803217193523211

theorem tailTrace_6243709 : CollatzResearch.WordTrace tailWord_6243709 prefixEnd_6243709 3206023783803217193523211 := by
  unfold tailWord_6243709
  simp only [CollatzResearch.WordTrace]
  refine ⟨227726775737116108446598181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151817850491410738964398787 227726775737116108446598181)
  ·
    refine ⟨42698770450709270333737159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227726775737116108446598181 42698770450709270333737159)
    ·
      refine ⟨64048155676063905500605739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42698770450709270333737159 64048155676063905500605739)
      ·
        refine ⟨96072233514095858250908609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64048155676063905500605739 96072233514095858250908609)
        ·
          refine ⟨72054175135571893688181457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96072233514095858250908609 72054175135571893688181457)
          ·
            refine ⟨54040631351678920266136093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72054175135571893688181457 54040631351678920266136093)
            ·
              refine ⟨20265236756879595099801035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54040631351678920266136093 20265236756879595099801035)
              ·
                refine ⟨30397855135319392649701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20265236756879595099801035 30397855135319392649701553)
                ·
                  refine ⟨22798391351489544487276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30397855135319392649701553 22798391351489544487276165)
                  ·
                    refine ⟨4274698378404289591364281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22798391351489544487276165 4274698378404289591364281)
                    ·
                      refine ⟨3206023783803217193523211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274698378404289591364281 3206023783803217193523211)
                      ·
                        rfl

theorem cell23_6243709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_6243709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243709 prefixEnd_6243709 := by exact prefixLift 6243709
  have htrace : WordTrace (prefixWord ++ tailWord_6243709) baseStart_6243709 baseEnd_6243709 := by
    simpa [prefixWord, tailWord_6243709, baseEnd_6243709] using wordTrace_append hprefix tailTrace_6243709
  have hstable : (prefixWord ++ tailWord_6243709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243709).length < 2 ^ (prefixWord ++ tailWord_6243709).sum := by decide
  have hdescent : baseEnd_6243709 < baseStart_6243709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243712 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_6243712 : Nat := 118140960795 + 6243712 * 2 ^ 59
def prefixEnd_6243712 : Nat := 4983230072969 + 3 ^ 40 * 6243712 * 2
def baseEnd_6243712 : Nat := 3206025324245180681785697

theorem tailTrace_6243712 : CollatzResearch.WordTrace tailWord_6243712 prefixEnd_6243712 3206025324245180681785697 := by
  unfold tailWord_6243712
  simp only [CollatzResearch.WordTrace]
  refine ⟨113863442578052619979478695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151817923437403493305971593 113863442578052619979478695)
  ·
    refine ⟨170795163867078929969218043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113863442578052619979478695 170795163867078929969218043)
    ·
      refine ⟨256192745800618394953827065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170795163867078929969218043 256192745800618394953827065)
      ·
        refine ⟨192144559350463796215370299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256192745800618394953827065 192144559350463796215370299)
        ·
          refine ⟨288216839025695694323055449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192144559350463796215370299 288216839025695694323055449)
          ·
            refine ⟨216162629269271770742291587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288216839025695694323055449 216162629269271770742291587)
            ·
              refine ⟨324243943903907656113437381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216162629269271770742291587 324243943903907656113437381)
              ·
                refine ⟨60795739481982685521269509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324243943903907656113437381 60795739481982685521269509)
                ·
                  refine ⟨11399201152871753535238033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60795739481982685521269509 11399201152871753535238033)
                  ·
                    refine ⟨8549400864653815151428525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11399201152871753535238033 8549400864653815151428525)
                    ·
                      refine ⟨3206025324245180681785697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549400864653815151428525 3206025324245180681785697)
                      ·
                        rfl

theorem cell23_6243712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_6243712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243712 prefixEnd_6243712 := by exact prefixLift 6243712
  have htrace : WordTrace (prefixWord ++ tailWord_6243712) baseStart_6243712 baseEnd_6243712 := by
    simpa [prefixWord, tailWord_6243712, baseEnd_6243712] using wordTrace_append hprefix tailTrace_6243712
  have hstable : (prefixWord ++ tailWord_6243712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243712).length < 2 ^ (prefixWord ++ tailWord_6243712).sum := by decide
  have hdescent : baseEnd_6243712 < baseStart_6243712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243719 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 3, 4]
def baseStart_6243719 : Nat := 118140960795 + 6243719 * 2 ^ 59
def prefixEnd_6243719 : Nat := 4983230072969 + 3 ^ 40 * 6243719 * 2
def baseEnd_6243719 : Nat := 1068676306203254051466055

theorem tailTrace_6243719 : CollatzResearch.WordTrace tailWord_6243719 prefixEnd_6243719 1068676306203254051466055 := by
  unfold tailWord_6243719
  simp only [CollatzResearch.WordTrace]
  refine ⟨227727140467079880154462211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151818093644719920102974807 227727140467079880154462211)
  ·
    refine ⟨341590710700619820231693317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227727140467079880154462211 341590710700619820231693317)
    ·
      refine ⟨64048258256366216293442497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341590710700619820231693317 64048258256366216293442497)
      ·
        refine ⟨48036193692274662220081873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64048258256366216293442497 48036193692274662220081873)
        ·
          refine ⟨36027145269205996665061405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48036193692274662220081873 36027145269205996665061405)
          ·
            refine ⟨13510179475952248749398027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36027145269205996665061405 13510179475952248749398027)
            ·
              refine ⟨20265269213928373124097041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13510179475952248749398027 20265269213928373124097041)
              ·
                refine ⟨15198951910446279843072781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20265269213928373124097041 15198951910446279843072781)
                ·
                  refine ⟨5699606966417354941152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15198951910446279843072781 5699606966417354941152293)
                  ·
                    refine ⟨1068676306203254051466055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699606966417354941152293 1068676306203254051466055)
                    ·
                      rfl

theorem cell23_6243719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_6243719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243719 prefixEnd_6243719 := by exact prefixLift 6243719
  have htrace : WordTrace (prefixWord ++ tailWord_6243719) baseStart_6243719 baseEnd_6243719 := by
    simpa [prefixWord, tailWord_6243719, baseEnd_6243719] using wordTrace_append hprefix tailTrace_6243719
  have hstable : (prefixWord ++ tailWord_6243719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243719).length < 2 ^ (prefixWord ++ tailWord_6243719).sum := by decide
  have hdescent : baseEnd_6243719 < baseStart_6243719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_6243755 : Nat := 118140960795 + 6243755 * 2 ^ 59
def prefixEnd_6243755 : Nat := 4983230072969 + 3 ^ 40 * 6243755 * 2
def baseEnd_6243755 : Nat := 3206047403913324013547999

theorem tailTrace_6243755 : CollatzResearch.WordTrace tailWord_6243755 prefixEnd_6243755 3206047403913324013547999 := by
  unfold tailWord_6243755
  simp only [CollatzResearch.WordTrace]
  refine ⟨227728453494949458302772719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151818968996632972201848479 227728453494949458302772719)
  ·
    refine ⟨341592680242424187454159079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227728453494949458302772719 341592680242424187454159079)
    ·
      refine ⟨512389020363636281181238619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341592680242424187454159079 512389020363636281181238619)
      ·
        refine ⟨768583530545454421771857929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512389020363636281181238619 768583530545454421771857929)
        ·
          refine ⟨576437647909090816328893447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768583530545454421771857929 576437647909090816328893447)
          ·
            refine ⟨864656471863636224493340171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576437647909090816328893447 864656471863636224493340171)
            ·
              refine ⟨1296984707795454336740010257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864656471863636224493340171 1296984707795454336740010257)
              ·
                refine ⟨972738530846590752555007693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296984707795454336740010257 972738530846590752555007693)
                ·
                  refine ⟨364776949067471532208127885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972738530846590752555007693 364776949067471532208127885)
                  ·
                    refine ⟨136791355900301824578047957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364776949067471532208127885 136791355900301824578047957)
                    ·
                      refine ⟨3206047403913324013547999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136791355900301824578047957 3206047403913324013547999)
                      ·
                        rfl

theorem cell23_6243755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_6243755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243755 prefixEnd_6243755 := by exact prefixLift 6243755
  have htrace : WordTrace (prefixWord ++ tailWord_6243755) baseStart_6243755 baseEnd_6243755 := by
    simpa [prefixWord, tailWord_6243755, baseEnd_6243755] using wordTrace_append hprefix tailTrace_6243755
  have hstable : (prefixWord ++ tailWord_6243755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243755).length < 2 ^ (prefixWord ++ tailWord_6243755).sum := by decide
  have hdescent : baseEnd_6243755 < baseStart_6243755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243762 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_6243762 : Nat := 118140960795 + 6243762 * 2 ^ 59
def prefixEnd_6243762 : Nat := 4983230072969 + 3 ^ 40 * 6243762 * 2
def baseEnd_6243762 : Nat := 1068683666092635162053489

theorem tailTrace_6243762 : CollatzResearch.WordTrace tailWord_6243762 prefixEnd_6243762 1068683666092635162053489 := by
  unfold tailWord_6243762
  simp only [CollatzResearch.WordTrace]
  refine ⟨56932177201481024624569385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151819139203949398998851693 56932177201481024624569385)
  ·
    refine ⟨42699132901110768468427039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56932177201481024624569385 42699132901110768468427039)
    ·
      refine ⟨64048699351666152702640559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42699132901110768468427039 64048699351666152702640559)
      ·
        refine ⟨96073049027499229053960839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64048699351666152702640559 96073049027499229053960839)
        ·
          refine ⟨144109573541248843580941259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96073049027499229053960839 144109573541248843580941259)
          ·
            refine ⟨216164360311873265371411889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144109573541248843580941259 216164360311873265371411889)
            ·
              refine ⟨162123270233904949028558917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216164360311873265371411889 162123270233904949028558917)
              ·
                refine ⟨30398113168857177942854797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162123270233904949028558917 30398113168857177942854797)
                ·
                  refine ⟨11399292438321441728570549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30398113168857177942854797 11399292438321441728570549)
                  ·
                    refine ⟨1068683666092635162053489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11399292438321441728570549 1068683666092635162053489)
                    ·
                      rfl

theorem cell23_6243762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_6243762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243762 prefixEnd_6243762 := by exact prefixLift 6243762
  have htrace : WordTrace (prefixWord ++ tailWord_6243762) baseStart_6243762 baseEnd_6243762 := by
    simpa [prefixWord, tailWord_6243762, baseEnd_6243762] using wordTrace_append hprefix tailTrace_6243762
  have hstable : (prefixWord ++ tailWord_6243762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243762).length < 2 ^ (prefixWord ++ tailWord_6243762).sum := by decide
  have hdescent : baseEnd_6243762 < baseStart_6243762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243809 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_6243809 : Nat := 118140960795 + 6243809 * 2 ^ 59
def prefixEnd_6243809 : Nat := 4983230072969 + 3 ^ 40 * 6243809 * 2
def baseEnd_6243809 : Nat := 1068691710622888934090917

theorem tailTrace_6243809 : CollatzResearch.WordTrace tailWord_6243809 prefixEnd_6243809 1068691710622888934090917 := by
  unfold tailWord_6243809
  simp only [CollatzResearch.WordTrace]
  refine ⟨227730423036753825525238481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151820282024502550350158987 227730423036753825525238481)
  ·
    refine ⟨170797817277565369143928861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227730423036753825525238481 170797817277565369143928861)
    ·
      refine ⟨64049181479087013428973323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170797817277565369143928861 64049181479087013428973323)
      ·
        refine ⟨96073772218630520143459985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64049181479087013428973323 96073772218630520143459985)
        ·
          refine ⟨72055329163972890107594989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96073772218630520143459985 72055329163972890107594989)
          ·
            refine ⟨27020748436489833790348121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72055329163972890107594989 27020748436489833790348121)
            ·
              refine ⟨20265561327367375342761091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27020748436489833790348121 20265561327367375342761091)
              ·
                refine ⟨30398341991051063014141637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20265561327367375342761091 30398341991051063014141637)
                ·
                  refine ⟨5699689123322074315151557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30398341991051063014141637 5699689123322074315151557)
                  ·
                    refine ⟨1068691710622888934090917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699689123322074315151557 1068691710622888934090917)
                    ·
                      rfl

theorem cell23_6243809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_6243809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243809 prefixEnd_6243809 := by exact prefixLift 6243809
  have htrace : WordTrace (prefixWord ++ tailWord_6243809) baseStart_6243809 baseEnd_6243809 := by
    simpa [prefixWord, tailWord_6243809, baseEnd_6243809] using wordTrace_append hprefix tailTrace_6243809
  have hstable : (prefixWord ++ tailWord_6243809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243809).length < 2 ^ (prefixWord ++ tailWord_6243809).sum := by decide
  have hdescent : baseEnd_6243809 < baseStart_6243809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243836 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_6243836 : Nat := 118140960795 + 6243836 * 2 ^ 59
def prefixEnd_6243836 : Nat := 4983230072969 + 3 ^ 40 * 6243836 * 2
def baseEnd_6243836 : Nat := 3206088995846338196635127

theorem tailTrace_6243836 : CollatzResearch.WordTrace tailWord_6243836 prefixEnd_6243836 3206088995846338196635127 := by
  unfold tailWord_6243836
  simp only [CollatzResearch.WordTrace]
  refine ⟨113865703903828004568235681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151820938538437339424314241 113865703903828004568235681)
  ·
    refine ⟨85399277927871003426176761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113865703903828004568235681 85399277927871003426176761)
    ·
      refine ⟨64049458445903252569632571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85399277927871003426176761 64049458445903252569632571)
      ·
        refine ⟨96074187668854878854448857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64049458445903252569632571 96074187668854878854448857)
        ·
          refine ⟨72055640751641159140836643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96074187668854878854448857 72055640751641159140836643)
          ·
            refine ⟨108083461127461738711254965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72055640751641159140836643 108083461127461738711254965)
            ·
              refine ⟨10132824480699538004180153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108083461127461738711254965 10132824480699538004180153)
              ·
                refine ⟨7599618360524653503135115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132824480699538004180153 7599618360524653503135115)
                ·
                  refine ⟨11399427540786980254702673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599618360524653503135115 11399427540786980254702673)
                  ·
                    refine ⟨8549570655590235191027005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11399427540786980254702673 8549570655590235191027005)
                    ·
                      refine ⟨3206088995846338196635127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549570655590235191027005 3206088995846338196635127)
                      ·
                        rfl

theorem cell23_6243836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_6243836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243836 prefixEnd_6243836 := by exact prefixLift 6243836
  have htrace : WordTrace (prefixWord ++ tailWord_6243836) baseStart_6243836 baseEnd_6243836 := by
    simpa [prefixWord, tailWord_6243836, baseEnd_6243836] using wordTrace_append hprefix tailTrace_6243836
  have hstable : (prefixWord ++ tailWord_6243836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243836).length < 2 ^ (prefixWord ++ tailWord_6243836).sum := by decide
  have hdescent : baseEnd_6243836 < baseStart_6243836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243849 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_6243849 : Nat := 118140960795 + 6243849 * 2 ^ 59
def prefixEnd_6243849 : Nat := 4983230072969 + 3 ^ 40 * 6243849 * 2
def baseEnd_6243849 : Nat := 3206095671094846645772567

theorem tailTrace_6243849 : CollatzResearch.WordTrace tailWord_6243849 prefixEnd_6243849 3206095671094846645772567 := by
  unfold tailWord_6243849
  simp only [CollatzResearch.WordTrace]
  refine ⟨227731881956608912356694601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151821254637739274904463067 227731881956608912356694601)
  ·
    refine ⟨170798911467456684267520951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227731881956608912356694601 170798911467456684267520951)
    ·
      refine ⟨256198367201185026401281427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170798911467456684267520951 256198367201185026401281427)
      ·
        refine ⟨384297550801777539601922141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256198367201185026401281427 384297550801777539601922141)
        ·
          refine ⟨144111581550666577350720803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384297550801777539601922141 144111581550666577350720803)
          ·
            refine ⟨216167372325999866026081205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144111581550666577350720803 216167372325999866026081205)
            ·
              refine ⟨20265691155562487439945113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216167372325999866026081205 20265691155562487439945113)
              ·
                refine ⟨15199268366671865579958835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20265691155562487439945113 15199268366671865579958835)
                ·
                  refine ⟨22798902550007798369938253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15199268366671865579958835 22798902550007798369938253)
                  ·
                    refine ⟨8549588456252924388726845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22798902550007798369938253 8549588456252924388726845)
                    ·
                      refine ⟨3206095671094846645772567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549588456252924388726845 3206095671094846645772567)
                      ·
                        rfl

theorem cell23_6243849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_6243849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243849 prefixEnd_6243849 := by exact prefixLift 6243849
  have htrace : WordTrace (prefixWord ++ tailWord_6243849) baseStart_6243849 baseEnd_6243849 := by
    simpa [prefixWord, tailWord_6243849, baseEnd_6243849] using wordTrace_append hprefix tailTrace_6243849
  have hstable : (prefixWord ++ tailWord_6243849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243849).length < 2 ^ (prefixWord ++ tailWord_6243849).sum := by decide
  have hdescent : baseEnd_6243849 < baseStart_6243849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243860 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6243860 : Nat := 118140960795 + 6243860 * 2 ^ 59
def prefixEnd_6243860 : Nat := 4983230072969 + 3 ^ 40 * 6243860 * 2
def baseEnd_6243860 : Nat := 1068700439794015367578339

theorem tailTrace_6243860 : CollatzResearch.WordTrace tailWord_6243860 prefixEnd_6243860 1068700439794015367578339 := by
  unfold tailWord_6243860
  simp only [CollatzResearch.WordTrace]
  refine ⟨113866141579784530617672517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151821522106379374156896689 113866141579784530617672517)
  ·
    refine ⟨21349901546209599490813597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113866141579784530617672517 21349901546209599490813597)
    ·
      refine ⟨8006213079828599809055099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21349901546209599490813597 8006213079828599809055099)
      ·
        refine ⟨12009319619742899713582649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006213079828599809055099 12009319619742899713582649)
        ·
          refine ⟨9006989714807174785186987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12009319619742899713582649 9006989714807174785186987)
          ·
            refine ⟨13510484572210762177780481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9006989714807174785186987 13510484572210762177780481)
            ·
              refine ⟨10132863429158071633335361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13510484572210762177780481 10132863429158071633335361)
              ·
                refine ⟨7599647571868553725001521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132863429158071633335361 7599647571868553725001521)
                ·
                  refine ⟨5699735678901415293751141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599647571868553725001521 5699735678901415293751141)
                  ·
                    refine ⟨1068700439794015367578339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699735678901415293751141 1068700439794015367578339)
                    ·
                      rfl

theorem cell23_6243860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6243860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243860 prefixEnd_6243860 := by exact prefixLift 6243860
  have htrace : WordTrace (prefixWord ++ tailWord_6243860) baseStart_6243860 baseEnd_6243860 := by
    simpa [prefixWord, tailWord_6243860, baseEnd_6243860] using wordTrace_append hprefix tailTrace_6243860
  have hstable : (prefixWord ++ tailWord_6243860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243860).length < 2 ^ (prefixWord ++ tailWord_6243860).sum := by decide
  have hdescent : baseEnd_6243860 < baseStart_6243860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243917 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6243917 : Nat := 118140960795 + 6243917 * 2 ^ 59
def prefixEnd_6243917 : Nat := 4983230072969 + 3 ^ 40 * 6243917 * 2
def baseEnd_6243917 : Nat := 3206130587779352379722255

theorem tailTrace_6243917 : CollatzResearch.WordTrace tailWord_6243917 prefixEnd_6243917 3206130587779352379722255 := by
  unfold tailWord_6243917
  simp only [CollatzResearch.WordTrace]
  refine ⟨227734362120362559970170005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151822908080241706646780003 227734362120362559970170005)
  ·
    refine ⟨10675048224391994998601719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227734362120362559970170005 10675048224391994998601719)
    ·
      refine ⟨16012572336587992497902579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10675048224391994998601719 16012572336587992497902579)
      ·
        refine ⟨24018858504881988746853869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16012572336587992497902579 24018858504881988746853869)
        ·
          refine ⟨9007071939330745780070201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24018858504881988746853869 9007071939330745780070201)
          ·
            refine ⟨6755303954498059335052651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007071939330745780070201 6755303954498059335052651)
            ·
              refine ⟨10132955931747089002578977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755303954498059335052651 10132955931747089002578977)
              ·
                refine ⟨7599716948810316751934233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132955931747089002578977 7599716948810316751934233)
                ·
                  refine ⟨5699787711607737563950675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599716948810316751934233 5699787711607737563950675)
                  ·
                    refine ⟨8549681567411606345926013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5699787711607737563950675 8549681567411606345926013)
                    ·
                      refine ⟨3206130587779352379722255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549681567411606345926013 3206130587779352379722255)
                      ·
                        rfl

theorem cell23_6243917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6243917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243917 prefixEnd_6243917 := by exact prefixLift 6243917
  have htrace : WordTrace (prefixWord ++ tailWord_6243917) baseStart_6243917 baseEnd_6243917 := by
    simpa [prefixWord, tailWord_6243917, baseEnd_6243917] using wordTrace_append hprefix tailTrace_6243917
  have hstable : (prefixWord ++ tailWord_6243917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243917).length < 2 ^ (prefixWord ++ tailWord_6243917).sum := by decide
  have hdescent : baseEnd_6243917 < baseStart_6243917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6243959 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 2, 5]
def baseStart_6243959 : Nat := 118140960795 + 6243959 * 2 ^ 59
def prefixEnd_6243959 : Nat := 4983230072969 + 3 ^ 40 * 6243959 * 2
def baseEnd_6243959 : Nat := 1068717384655613738465687

theorem tailTrace_6243959 : CollatzResearch.WordTrace tailWord_6243959 prefixEnd_6243959 1068717384655613738465687 := by
  unfold tailWord_6243959
  simp only [CollatzResearch.WordTrace]
  refine ⟨227735893986210401143198931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151823929324140267428799287 227735893986210401143198931)
  ·
    refine ⟨341603840979315601714798397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227735893986210401143198931 341603840979315601714798397)
    ·
      refine ⟨128101440367243350643049399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341603840979315601714798397 128101440367243350643049399)
      ·
        refine ⟨192152160550865025964574099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128101440367243350643049399 192152160550865025964574099)
        ·
          refine ⟨288228240826297538946861149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192152160550865025964574099 288228240826297538946861149)
          ·
            refine ⟨108085590309861577105072931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288228240826297538946861149 108085590309861577105072931)
            ·
              refine ⟨162128385464792365657609397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108085590309861577105072931 162128385464792365657609397)
              ·
                refine ⟨15199536137324284280400881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162128385464792365657609397 15199536137324284280400881)
                ·
                  refine ⟨11399652102993213210300661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199536137324284280400881 11399652102993213210300661)
                  ·
                    refine ⟨1068717384655613738465687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11399652102993213210300661 1068717384655613738465687)
                    ·
                      rfl

theorem cell23_6243959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_6243959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6243959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6243959 prefixEnd_6243959 := by exact prefixLift 6243959
  have htrace : WordTrace (prefixWord ++ tailWord_6243959) baseStart_6243959 baseEnd_6243959 := by
    simpa [prefixWord, tailWord_6243959, baseEnd_6243959] using wordTrace_append hprefix tailTrace_6243959
  have hstable : (prefixWord ++ tailWord_6243959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6243959).length < 2 ^ (prefixWord ++ tailWord_6243959).sum := by decide
  have hdescent : baseEnd_6243959 < baseStart_6243959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6243959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244013 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6244013 : Nat := 118140960795 + 6244013 * 2 ^ 59
def prefixEnd_6244013 : Nat := 4983230072969 + 3 ^ 40 * 6244013 * 2
def baseEnd_6244013 : Nat := 3206179881922184004121813

theorem tailTrace_6244013 : CollatzResearch.WordTrace tailWord_6244013 prefixEnd_6244013 3206179881922184004121813 := by
  unfold tailWord_6244013
  simp only [CollatzResearch.WordTrace]
  refine ⟨227737863528014768365664693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151825242352009845577109795 227737863528014768365664693)
  ·
    refine ⟨21350424705751384534281065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227737863528014768365664693 21350424705751384534281065)
    ·
      refine ⟨16012818529313538400710799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21350424705751384534281065 16012818529313538400710799)
      ·
        refine ⟨24019227793970307601066199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16012818529313538400710799 24019227793970307601066199)
        ·
          refine ⟨36028841690955461401599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24019227793970307601066199 36028841690955461401599299)
          ·
            refine ⟨54043262536433192102398949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36028841690955461401599299 54043262536433192102398949)
            ·
              refine ⟨10133111725581223519199803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54043262536433192102398949 10133111725581223519199803)
              ·
                refine ⟨15199667588371835278799705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133111725581223519199803 15199667588371835278799705)
                ·
                  refine ⟨11399750691278876459099779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199667588371835278799705 11399750691278876459099779)
                  ·
                    refine ⟨17099626036918314688649669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11399750691278876459099779 17099626036918314688649669)
                    ·
                      refine ⟨3206179881922184004121813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17099626036918314688649669 3206179881922184004121813)
                      ·
                        rfl

theorem cell23_6244013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6244013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244013 prefixEnd_6244013 := by exact prefixLift 6244013
  have htrace : WordTrace (prefixWord ++ tailWord_6244013) baseStart_6244013 baseEnd_6244013 := by
    simpa [prefixWord, tailWord_6244013, baseEnd_6244013] using wordTrace_append hprefix tailTrace_6244013
  have hstable : (prefixWord ++ tailWord_6244013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244013).length < 2 ^ (prefixWord ++ tailWord_6244013).sum := by decide
  have hdescent : baseEnd_6244013 < baseStart_6244013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244016 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_6244016 : Nat := 118140960795 + 6244016 * 2 ^ 59
def prefixEnd_6244016 : Nat := 4983230072969 + 3 ^ 40 * 6244016 * 2
def baseEnd_6244016 : Nat := 3206181422364147492384299

theorem tailTrace_6244016 : CollatzResearch.WordTrace tailWord_6244016 prefixEnd_6244016 3206181422364147492384299 := by
  unfold tailWord_6244016
  simp only [CollatzResearch.WordTrace]
  refine ⟨113868986473501949939011951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151825315298002599918682601 113868986473501949939011951)
  ·
    refine ⟨170803479710252924908517927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113868986473501949939011951 170803479710252924908517927)
    ·
      refine ⟨256205219565379387362776891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170803479710252924908517927 256205219565379387362776891)
      ·
        refine ⟨384307829348069081044165337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256205219565379387362776891 384307829348069081044165337)
        ·
          refine ⟨288230872011051810783124003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384307829348069081044165337 288230872011051810783124003)
          ·
            refine ⟨432346308016577716174686005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288230872011051810783124003 432346308016577716174686005)
            ·
              refine ⟨40532466376554160891376813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 432346308016577716174686005 40532466376554160891376813)
              ·
                refine ⟨15199674891207810334266305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40532466376554160891376813 15199674891207810334266305)
                ·
                  refine ⟨11399756168405857750699729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199674891207810334266305 11399756168405857750699729)
                  ·
                    refine ⟨8549817126304393313024797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11399756168405857750699729 8549817126304393313024797)
                    ·
                      refine ⟨3206181422364147492384299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549817126304393313024797 3206181422364147492384299)
                      ·
                        rfl

theorem cell23_6244016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_6244016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244016 prefixEnd_6244016 := by exact prefixLift 6244016
  have htrace : WordTrace (prefixWord ++ tailWord_6244016) baseStart_6244016 baseEnd_6244016 := by
    simpa [prefixWord, tailWord_6244016, baseEnd_6244016] using wordTrace_append hprefix tailTrace_6244016
  have hstable : (prefixWord ++ tailWord_6244016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244016).length < 2 ^ (prefixWord ++ tailWord_6244016).sum := by decide
  have hdescent : baseEnd_6244016 < baseStart_6244016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244039 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6244039 : Nat := 118140960795 + 6244039 * 2 ^ 59
def prefixEnd_6244039 : Nat := 4983230072969 + 3 ^ 40 * 6244039 * 2
def baseEnd_6244039 : Nat := 3206193232419200902396693

theorem tailTrace_6244039 : CollatzResearch.WordTrace tailWord_6244039 prefixEnd_6244039 3206193232419200902396693 := by
  unfold tailWord_6244039
  simp only [CollatzResearch.WordTrace]
  refine ⟨227738811825920574806111171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151825874550613716537407447 227738811825920574806111171)
  ·
    refine ⟨341608217738880862209166757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227738811825920574806111171 341608217738880862209166757)
    ·
      refine ⟨64051540826040161664218767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341608217738880862209166757 64051540826040161664218767)
      ·
        refine ⟨96077311239060242496328151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64051540826040161664218767 96077311239060242496328151)
        ·
          refine ⟨144115966858590363744492227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96077311239060242496328151 144115966858590363744492227)
          ·
            refine ⟨216173950287885545616738341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144115966858590363744492227 216173950287885545616738341)
            ·
              refine ⟨40532615678978539803138439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216173950287885545616738341 40532615678978539803138439)
              ·
                refine ⟨60798923518467809704707659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40532615678978539803138439 60798923518467809704707659)
                ·
                  refine ⟨91198385277701714557061489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60798923518467809704707659 91198385277701714557061489)
                  ·
                    refine ⟨68398788958276285917796117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91198385277701714557061489 68398788958276285917796117)
                    ·
                      refine ⟨3206193232419200902396693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68398788958276285917796117 3206193232419200902396693)
                      ·
                        rfl

theorem cell23_6244039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6244039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244039 prefixEnd_6244039 := by exact prefixLift 6244039
  have htrace : WordTrace (prefixWord ++ tailWord_6244039) baseStart_6244039 baseEnd_6244039 := by
    simpa [prefixWord, tailWord_6244039, baseEnd_6244039] using wordTrace_append hprefix tailTrace_6244039
  have hstable : (prefixWord ++ tailWord_6244039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244039).length < 2 ^ (prefixWord ++ tailWord_6244039).sum := by decide
  have hdescent : baseEnd_6244039 < baseStart_6244039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244063 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_6244063 : Nat := 118140960795 + 6244063 * 2 ^ 59
def prefixEnd_6244063 : Nat := 4983230072969 + 3 ^ 40 * 6244063 * 2
def baseEnd_6244063 : Nat := 3206205555954908808496583

theorem tailTrace_6244063 : CollatzResearch.WordTrace tailWord_6244063 prefixEnd_6244063 3206205555954908808496583 := by
  unfold tailWord_6244063
  simp only [CollatzResearch.WordTrace]
  refine ⟨227739687177833626904984843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151826458118555751269989895 227739687177833626904984843)
  ·
    refine ⟨341609530766750440357477265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227739687177833626904984843 341609530766750440357477265)
    ·
      refine ⟨256207148075062830268107949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341609530766750440357477265 256207148075062830268107949)
      ·
        refine ⟨96077680528148561350540481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256207148075062830268107949 96077680528148561350540481)
        ·
          refine ⟨72058260396111421012905361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96077680528148561350540481 72058260396111421012905361)
          ·
            refine ⟨54043695297083565759679021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72058260396111421012905361 54043695297083565759679021)
            ·
              refine ⟨20266385736406337159879633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54043695297083565759679021 20266385736406337159879633)
              ·
                refine ⟨15199789302304752869909725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20266385736406337159879633 15199789302304752869909725)
                ·
                  refine ⟨5699920988364282326216147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15199789302304752869909725 5699920988364282326216147)
                  ·
                    refine ⟨8549881482546423489324221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5699920988364282326216147 8549881482546423489324221)
                    ·
                      refine ⟨3206205555954908808496583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549881482546423489324221 3206205555954908808496583)
                      ·
                        rfl

theorem cell23_6244063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_6244063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244063 prefixEnd_6244063 := by exact prefixLift 6244063
  have htrace : WordTrace (prefixWord ++ tailWord_6244063) baseStart_6244063 baseEnd_6244063 := by
    simpa [prefixWord, tailWord_6244063, baseEnd_6244063] using wordTrace_append hprefix tailTrace_6244063
  have hstable : (prefixWord ++ tailWord_6244063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244063).length < 2 ^ (prefixWord ++ tailWord_6244063).sum := by decide
  have hdescent : baseEnd_6244063 < baseStart_6244063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244067 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6244067 : Nat := 118140960795 + 6244067 * 2 ^ 59
def prefixEnd_6244067 : Nat := 4983230072969 + 3 ^ 40 * 6244067 * 2
def baseEnd_6244067 : Nat := 3206207609877526792846565

theorem tailTrace_6244067 : CollatzResearch.WordTrace tailWord_6244067 prefixEnd_6244067 3206207609877526792846565 := by
  unfold tailWord_6244067
  simp only [CollatzResearch.WordTrace]
  refine ⟨227739833069819135588130455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151826555379879423725420303 227739833069819135588130455)
  ·
    refine ⟨341609749604728703382195683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227739833069819135588130455 341609749604728703382195683)
    ·
      refine ⟨512414624407093055073293525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341609749604728703382195683 512414624407093055073293525)
      ·
        refine ⟨12009717759541243478280317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 512414624407093055073293525 12009717759541243478280317)
        ·
          refine ⟨4503644159827966304355119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12009717759541243478280317 4503644159827966304355119)
          ·
            refine ⟨6755466239741949456532679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503644159827966304355119 6755466239741949456532679)
            ·
              refine ⟨10133199359612924184799019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755466239741949456532679 10133199359612924184799019)
              ·
                refine ⟨15199799039419386277198529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133199359612924184799019 15199799039419386277198529)
                ·
                  refine ⟨11399849279564539707898897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199799039419386277198529 11399849279564539707898897)
                  ·
                    refine ⟨8549886959673404780924173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11399849279564539707898897 8549886959673404780924173)
                    ·
                      refine ⟨3206207609877526792846565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8549886959673404780924173 3206207609877526792846565)
                      ·
                        rfl

theorem cell23_6244067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6244067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244067 prefixEnd_6244067 := by exact prefixLift 6244067
  have htrace : WordTrace (prefixWord ++ tailWord_6244067) baseStart_6244067 baseEnd_6244067 := by
    simpa [prefixWord, tailWord_6244067, baseEnd_6244067] using wordTrace_append hprefix tailTrace_6244067
  have hstable : (prefixWord ++ tailWord_6244067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244067).length < 2 ^ (prefixWord ++ tailWord_6244067).sum := by decide
  have hdescent : baseEnd_6244067 < baseStart_6244067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244083 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 1, 5]
def baseStart_6244083 : Nat := 118140960795 + 6244083 * 2 ^ 59
def prefixEnd_6244083 : Nat := 4983230072969 + 3 ^ 40 * 6244083 * 2
def baseEnd_6244083 : Nat := 1068738608522666243415497

theorem tailTrace_6244083 : CollatzResearch.WordTrace tailWord_6244083 prefixEnd_6244083 1068738608522666243415497 := by
  unfold tailWord_6244083
  simp only [CollatzResearch.WordTrace]
  refine ⟨227740416637761170320712903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151826944425174113547141935 227740416637761170320712903)
  ·
    refine ⟨341610624956641755481069355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227740416637761170320712903 341610624956641755481069355)
    ·
      refine ⟨512415937434962633221604033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341610624956641755481069355 512415937434962633221604033)
      ·
        refine ⟨384311953076221974916203025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512415937434962633221604033 384311953076221974916203025)
        ·
          refine ⟨288233964807166481187152269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384311953076221974916203025 288233964807166481187152269)
          ·
            refine ⟨108087736802687430445182101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288233964807166481187152269 108087736802687430445182101)
            ·
              refine ⟨5066612662625973302117911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108087736802687430445182101 5066612662625973302117911)
              ·
                refine ⟨7599918993938959953176867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066612662625973302117911 7599918993938959953176867)
                ·
                  refine ⟨11399878490908439929765301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599918993938959953176867 11399878490908439929765301)
                  ·
                    refine ⟨1068738608522666243415497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11399878490908439929765301 1068738608522666243415497)
                    ·
                      rfl

theorem cell23_6244083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 5].length) (baseStart_6244083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244083 prefixEnd_6244083 := by exact prefixLift 6244083
  have htrace : WordTrace (prefixWord ++ tailWord_6244083) baseStart_6244083 baseEnd_6244083 := by
    simpa [prefixWord, tailWord_6244083, baseEnd_6244083] using wordTrace_append hprefix tailTrace_6244083
  have hstable : (prefixWord ++ tailWord_6244083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244083).length < 2 ^ (prefixWord ++ tailWord_6244083).sum := by decide
  have hdescent : baseEnd_6244083 < baseStart_6244083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244096 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_6244096 : Nat := 118140960795 + 6244096 * 2 ^ 59
def prefixEnd_6244096 : Nat := 4983230072969 + 3 ^ 40 * 6244096 * 2
def baseEnd_6244096 : Nat := 1068740833605502393127977

theorem tailTrace_6244096 : CollatzResearch.WordTrace tailWord_6244096 prefixEnd_6244096 1068740833605502393127977 := by
  unfold tailWord_6244096
  simp only [CollatzResearch.WordTrace]
  refine ⟨113870445393357036770468071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151827260524476049027290761 113870445393357036770468071)
  ·
    refine ⟨170805668090035555155702107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113870445393357036770468071 170805668090035555155702107)
    ·
      refine ⟨256208502135053332733553161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170805668090035555155702107 256208502135053332733553161)
      ·
        refine ⟨192156376601289999550164871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256208502135053332733553161 192156376601289999550164871)
        ·
          refine ⟨288234564901934999325247307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192156376601289999550164871 288234564901934999325247307)
          ·
            refine ⟨432351847352902498987870961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288234564901934999325247307 432351847352902498987870961)
            ·
              refine ⟨324263885514676874240903221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432351847352902498987870961 324263885514676874240903221)
              ·
                refine ⟨30399739267000956960084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324263885514676874240903221 30399739267000956960084677)
                ·
                  refine ⟨5699951112562679430015877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30399739267000956960084677 5699951112562679430015877)
                  ·
                    refine ⟨1068740833605502393127977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699951112562679430015877 1068740833605502393127977)
                    ·
                      rfl

theorem cell23_6244096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_6244096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244096 prefixEnd_6244096 := by exact prefixLift 6244096
  have htrace : WordTrace (prefixWord ++ tailWord_6244096) baseStart_6244096 baseEnd_6244096 := by
    simpa [prefixWord, tailWord_6244096, baseEnd_6244096] using wordTrace_append hprefix tailTrace_6244096
  have hstable : (prefixWord ++ tailWord_6244096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244096).length < 2 ^ (prefixWord ++ tailWord_6244096).sum := by decide
  have hdescent : baseEnd_6244096 < baseStart_6244096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244106 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6244106 : Nat := 118140960795 + 6244106 * 2 ^ 59
def prefixEnd_6244106 : Nat := 4983230072969 + 3 ^ 40 * 6244106 * 2
def baseEnd_6244106 : Nat := 3206227635623052140258885

theorem tailTrace_6244106 : CollatzResearch.WordTrace tailWord_6244106 prefixEnd_6244106 3206227635623052140258885 := by
  unfold tailWord_6244106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56935313879169461312200043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151827503677785230165866781 56935313879169461312200043)
  ·
    refine ⟨85402970818754191968300065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56935313879169461312200043 85402970818754191968300065)
    ·
      refine ⟨64052228114065643976225049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85402970818754191968300065 64052228114065643976225049)
      ·
        refine ⟨48039171085549232982168787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64052228114065643976225049 48039171085549232982168787)
        ·
          refine ⟨72058756628323849473253181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48039171085549232982168787 72058756628323849473253181)
          ·
            refine ⟨27022033735621443552469943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72058756628323849473253181 27022033735621443552469943)
            ·
              refine ⟨40533050603432165328704915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27022033735621443552469943 40533050603432165328704915)
              ·
                refine ⟨60799575905148247993057373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40533050603432165328704915 60799575905148247993057373)
                ·
                  refine ⟨22799840964430592997396515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60799575905148247993057373 22799840964430592997396515)
                  ·
                    refine ⟨34199761446645889496094773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22799840964430592997396515 34199761446645889496094773)
                    ·
                      refine ⟨3206227635623052140258885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34199761446645889496094773 3206227635623052140258885)
                      ·
                        rfl

theorem cell23_6244106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6244106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244106 prefixEnd_6244106 := by exact prefixLift 6244106
  have htrace : WordTrace (prefixWord ++ tailWord_6244106) baseStart_6244106 baseEnd_6244106 := by
    simpa [prefixWord, tailWord_6244106, baseEnd_6244106] using wordTrace_append hprefix tailTrace_6244106
  have hstable : (prefixWord ++ tailWord_6244106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244106).length < 2 ^ (prefixWord ++ tailWord_6244106).sum := by decide
  have hdescent : baseEnd_6244106 < baseStart_6244106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244120 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6244120 : Nat := 118140960795 + 6244120 * 2 ^ 59
def prefixEnd_6244120 : Nat := 4983230072969 + 3 ^ 40 * 6244120 * 2
def baseEnd_6244120 : Nat := 3206234824352215085483821

theorem tailTrace_6244120 : CollatzResearch.WordTrace tailWord_6244120 prefixEnd_6244120 3206234824352215085483821 := by
  unfold tailWord_6244120
  simp only [CollatzResearch.WordTrace]
  refine ⟨113870883069313562819904907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151827844092418083759873209 113870883069313562819904907)
  ·
    refine ⟨170806324603970344229857361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113870883069313562819904907 170806324603970344229857361)
    ·
      refine ⟨128104743452977758172393021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170806324603970344229857361 128104743452977758172393021)
      ·
        refine ⟨48039278794866659314647383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128104743452977758172393021 48039278794866659314647383)
        ·
          refine ⟨72058918192299988971971075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48039278794866659314647383 72058918192299988971971075)
          ·
            refine ⟨108088377288449983457956613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72058918192299988971971075 108088377288449983457956613)
            ·
              refine ⟨20266570741584371898366865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108088377288449983457956613 20266570741584371898366865)
              ·
                refine ⟨15199928056188278923775149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20266570741584371898366865 15199928056188278923775149)
                ·
                  refine ⟨5699973021070604596415681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15199928056188278923775149 5699973021070604596415681)
                  ·
                    refine ⟨4274979765802953447311761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699973021070604596415681 4274979765802953447311761)
                    ·
                      refine ⟨3206234824352215085483821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4274979765802953447311761 3206234824352215085483821)
                      ·
                        rfl

theorem cell23_6244120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6244120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244120 prefixEnd_6244120 := by exact prefixLift 6244120
  have htrace : WordTrace (prefixWord ++ tailWord_6244120) baseStart_6244120 baseEnd_6244120 := by
    simpa [prefixWord, tailWord_6244120, baseEnd_6244120] using wordTrace_append hprefix tailTrace_6244120
  have hstable : (prefixWord ++ tailWord_6244120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244120).length < 2 ^ (prefixWord ++ tailWord_6244120).sum := by decide
  have hdescent : baseEnd_6244120 < baseStart_6244120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244170 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_6244170 : Nat := 118140960795 + 6244170 * 2 ^ 59
def prefixEnd_6244170 : Nat := 4983230072969 + 3 ^ 40 * 6244170 * 2
def baseEnd_6244170 : Nat := 3206260498384939889858591

theorem tailTrace_6244170 : CollatzResearch.WordTrace tailWord_6244170 prefixEnd_6244170 3206260498384939889858591 := by
  unfold tailWord_6244170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56935897447111496044782491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151829059858963989452753309 56935897447111496044782491)
  ·
    refine ⟨85403846170667244067173737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56935897447111496044782491 85403846170667244067173737)
    ·
      refine ⟨64052884628000433050380303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85403846170667244067173737 64052884628000433050380303)
      ·
        refine ⟨96079326942000649575570455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64052884628000433050380303 96079326942000649575570455)
        ·
          refine ⟨144118990413000974363355683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96079326942000649575570455 144118990413000974363355683)
          ·
            refine ⟨216178485619501461545033525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144118990413000974363355683 216178485619501461545033525)
            ·
              refine ⟨20266733026828262019846893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216178485619501461545033525 20266733026828262019846893)
              ·
                refine ⟨7600024885060598257442585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20266733026828262019846893 7600024885060598257442585)
                ·
                  refine ⟨5700018663795448693081939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7600024885060598257442585 5700018663795448693081939)
                  ·
                    refine ⟨8550027995693173039622909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5700018663795448693081939 8550027995693173039622909)
                    ·
                      refine ⟨3206260498384939889858591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8550027995693173039622909 3206260498384939889858591)
                      ·
                        rfl

theorem cell23_6244170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_6244170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244170 prefixEnd_6244170 := by exact prefixLift 6244170
  have htrace : WordTrace (prefixWord ++ tailWord_6244170) baseStart_6244170 baseEnd_6244170 := by
    simpa [prefixWord, tailWord_6244170, baseEnd_6244170] using wordTrace_append hprefix tailTrace_6244170
  have hstable : (prefixWord ++ tailWord_6244170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244170).length < 2 ^ (prefixWord ++ tailWord_6244170).sum := by decide
  have hdescent : baseEnd_6244170 < baseStart_6244170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244213 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6244213 : Nat := 118140960795 + 6244213 * 2 ^ 59
def prefixEnd_6244213 : Nat := 4983230072969 + 3 ^ 40 * 6244213 * 2
def baseEnd_6244213 : Nat := 3206282578053083221620893

theorem tailTrace_6244213 : CollatzResearch.WordTrace tailWord_6244213 prefixEnd_6244213 3206282578053083221620893 := by
  unfold tailWord_6244213
  simp only [CollatzResearch.WordTrace]
  refine ⟨227745158127290202522945293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151830105418193468348630195 227745158127290202522945293)
  ·
    refine ⟨85404434297733825946104485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227745158127290202522945293 85404434297733825946104485)
    ·
      refine ⟨16013331430825092364894591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85404434297733825946104485 16013331430825092364894591)
      ·
        refine ⟨24019997146237638547341887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013331430825092364894591 24019997146237638547341887)
        ·
          refine ⟨36029995719356457821012831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24019997146237638547341887 36029995719356457821012831)
          ·
            refine ⟨54044993579034686731519247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36029995719356457821012831 54044993579034686731519247)
            ·
              refine ⟨81067490368552030097278871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54044993579034686731519247 81067490368552030097278871)
              ·
                refine ⟨121601235552828045145918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81067490368552030097278871 121601235552828045145918307)
                ·
                  refine ⟨182401853329242067718877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121601235552828045145918307 182401853329242067718877461)
                  ·
                    refine ⟨8550086874808221924322381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182401853329242067718877461 8550086874808221924322381)
                    ·
                      refine ⟨3206282578053083221620893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8550086874808221924322381 3206282578053083221620893)
                      ·
                        rfl

theorem cell23_6244213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6244213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244213 prefixEnd_6244213 := by exact prefixLift 6244213
  have htrace : WordTrace (prefixWord ++ tailWord_6244213) baseStart_6244213 baseEnd_6244213 := by
    simpa [prefixWord, tailWord_6244213, baseEnd_6244213] using wordTrace_append hprefix tailTrace_6244213
  have hstable : (prefixWord ++ tailWord_6244213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244213).length < 2 ^ (prefixWord ++ tailWord_6244213).sum := by decide
  have hdescent : baseEnd_6244213 < baseStart_6244213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244227 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 2, 2, 2]
def baseStart_6244227 : Nat := 118140960795 + 6244227 * 2 ^ 59
def prefixEnd_6244227 : Nat := 4983230072969 + 3 ^ 40 * 6244227 * 2
def baseEnd_6244227 : Nat := 3206289766782246166845829

theorem tailTrace_6244227 : CollatzResearch.WordTrace tailWord_6244227 prefixEnd_6244227 3206289766782246166845829 := by
  unfold tailWord_6244227
  simp only [CollatzResearch.WordTrace]
  refine ⟨227745668749239482913954935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151830445832826321942636623 227745668749239482913954935)
  ·
    refine ⟨341618503123859224370932403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227745668749239482913954935 341618503123859224370932403)
    ·
      refine ⟨512427754685788836556398605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341618503123859224370932403 512427754685788836556398605)
      ·
        refine ⟨192160408007170813708649477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512427754685788836556398605 192160408007170813708649477)
        ·
          refine ⟨36030076501344527570371777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192160408007170813708649477 36030076501344527570371777)
          ·
            refine ⟨27022557376008395677778833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36030076501344527570371777 27022557376008395677778833)
            ·
              refine ⟨20266918032006296758334125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27022557376008395677778833 20266918032006296758334125)
              ·
                refine ⟨7600094262002361284375297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20266918032006296758334125 7600094262002361284375297)
                ·
                  refine ⟨5700070696501770963281473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7600094262002361284375297 5700070696501770963281473)
                  ·
                    refine ⟨4275053022376328222461105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700070696501770963281473 4275053022376328222461105)
                    ·
                      refine ⟨3206289766782246166845829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275053022376328222461105 3206289766782246166845829)
                      ·
                        rfl

theorem cell23_6244227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_6244227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244227 prefixEnd_6244227 := by exact prefixLift 6244227
  have htrace : WordTrace (prefixWord ++ tailWord_6244227) baseStart_6244227 baseEnd_6244227 := by
    simpa [prefixWord, tailWord_6244227, baseEnd_6244227] using wordTrace_append hprefix tailTrace_6244227
  have hstable : (prefixWord ++ tailWord_6244227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244227).length < 2 ^ (prefixWord ++ tailWord_6244227).sum := by decide
  have hdescent : baseEnd_6244227 < baseStart_6244227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244248 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6244248 : Nat := 118140960795 + 6244248 * 2 ^ 59
def prefixEnd_6244248 : Nat := 4983230072969 + 3 ^ 40 * 6244248 * 2
def baseEnd_6244248 : Nat := 3206300549875990584683233

theorem tailTrace_6244248 : CollatzResearch.WordTrace tailWord_6244248 prefixEnd_6244248 3206300549875990584683233 := by
  unfold tailWord_6244248
  simp only [CollatzResearch.WordTrace]
  refine ⟨113873217341081701750234699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151830956454775602333646265 113873217341081701750234699)
  ·
    refine ⟨170809826011622552625352049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113873217341081701750234699 170809826011622552625352049)
    ·
      refine ⟨128107369508716914469014037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170809826011622552625352049 128107369508716914469014037)
      ·
        refine ⟨6005032945721105365735033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128107369508716914469014037 6005032945721105365735033)
        ·
          refine ⟨4503774709290829024301275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005032945721105365735033 4503774709290829024301275)
          ·
            refine ⟨6755662063936243536451913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503774709290829024301275 6755662063936243536451913)
            ·
              refine ⟨5066746547952182652338935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6755662063936243536451913 5066746547952182652338935)
              ·
                refine ⟨7600119821928273978508403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066746547952182652338935 7600119821928273978508403)
                ·
                  refine ⟨11400179732892410967762605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600119821928273978508403 11400179732892410967762605)
                  ·
                    refine ⟨4275067399834654112910977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11400179732892410967762605 4275067399834654112910977)
                    ·
                      refine ⟨3206300549875990584683233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275067399834654112910977 3206300549875990584683233)
                      ·
                        rfl

theorem cell23_6244248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6244248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244248 prefixEnd_6244248 := by exact prefixLift 6244248
  have htrace : WordTrace (prefixWord ++ tailWord_6244248) baseStart_6244248 baseEnd_6244248 := by
    simpa [prefixWord, tailWord_6244248, baseEnd_6244248] using wordTrace_append hprefix tailTrace_6244248
  have hstable : (prefixWord ++ tailWord_6244248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244248).length < 2 ^ (prefixWord ++ tailWord_6244248).sum := by decide
  have hdescent : baseEnd_6244248 < baseStart_6244248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244250 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_6244250 : Nat := 118140960795 + 6244250 * 2 ^ 59
def prefixEnd_6244250 : Nat := 4983230072969 + 3 ^ 40 * 6244250 * 2
def baseEnd_6244250 : Nat := 356255730759699952984247

theorem tailTrace_6244250 : CollatzResearch.WordTrace tailWord_6244250 prefixEnd_6244250 356255730759699952984247 := by
  unfold tailWord_6244250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56936626907039039460510551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151831005085437438561361469 56936626907039039460510551)
  ·
    refine ⟨85404940360558559190765827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56936626907039039460510551 85404940360558559190765827)
    ·
      refine ⟨128107410540837838786148741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85404940360558559190765827 128107410540837838786148741)
      ·
        refine ⟨24020139476407094772402889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128107410540837838786148741 24020139476407094772402889)
        ·
          refine ⟨18015104607305321079302167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24020139476407094772402889 18015104607305321079302167)
          ·
            refine ⟨27022656910957981618953251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18015104607305321079302167 27022656910957981618953251)
            ·
              refine ⟨40533985366436972428429877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27022656910957981618953251 40533985366436972428429877)
              ·
                refine ⟨3800061128103466165165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40533985366436972428429877 3800061128103466165165301)
                ·
                  refine ⟨356255730759699952984247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800061128103466165165301 356255730759699952984247)
                  ·
                    rfl

theorem cell23_6244250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_6244250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244250 prefixEnd_6244250 := by exact prefixLift 6244250
  have htrace : WordTrace (prefixWord ++ tailWord_6244250) baseStart_6244250 baseEnd_6244250 := by
    simpa [prefixWord, tailWord_6244250, baseEnd_6244250] using wordTrace_append hprefix tailTrace_6244250
  have hstable : (prefixWord ++ tailWord_6244250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244250).length < 2 ^ (prefixWord ++ tailWord_6244250).sum := by decide
  have hdescent : baseEnd_6244250 < baseStart_6244250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244293 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_6244293 : Nat := 118140960795 + 6244293 * 2 ^ 59
def prefixEnd_6244293 : Nat := 4983230072969 + 3 ^ 40 * 6244293 * 2
def baseEnd_6244293 : Nat := 1068774552168480969540175

theorem tailTrace_6244293 : CollatzResearch.WordTrace tailWord_6244293 prefixEnd_6244293 1068774552168480969540175 := by
  unfold tailWord_6244293
  simp only [CollatzResearch.WordTrace]
  refine ⟨227748075967000376185857533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151832050644666917457238355 227748075967000376185857533)
  ·
    refine ⟨85405528487625141069696575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227748075967000376185857533 85405528487625141069696575)
    ·
      refine ⟨128108292731437711604544863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85405528487625141069696575 128108292731437711604544863)
      ·
        refine ⟨192162439097156567406817295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128108292731437711604544863 192162439097156567406817295)
        ·
          refine ⟨288243658645734851110225943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192162439097156567406817295 288243658645734851110225943)
          ·
            refine ⟨432365487968602276665338915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288243658645734851110225943 432365487968602276665338915)
            ·
              refine ⟨648548231952903414998008373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432365487968602276665338915 648548231952903414998008373)
              ·
                refine ⟨60801396745584695156063285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648548231952903414998008373 60801396745584695156063285)
                ·
                  refine ⟨5700130944898565170880933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60801396745584695156063285 5700130944898565170880933)
                  ·
                    refine ⟨1068774552168480969540175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700130944898565170880933 1068774552168480969540175)
                    ·
                      rfl

theorem cell23_6244293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_6244293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244293 prefixEnd_6244293 := by exact prefixLift 6244293
  have htrace : WordTrace (prefixWord ++ tailWord_6244293) baseStart_6244293 baseEnd_6244293 := by
    simpa [prefixWord, tailWord_6244293, baseEnd_6244293] using wordTrace_append hprefix tailTrace_6244293
  have hstable : (prefixWord ++ tailWord_6244293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244293).length < 2 ^ (prefixWord ++ tailWord_6244293).sum := by decide
  have hdescent : baseEnd_6244293 < baseStart_6244293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244303 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_6244303 : Nat := 118140960795 + 6244303 * 2 ^ 59
def prefixEnd_6244303 : Nat := 4983230072969 + 3 ^ 40 * 6244303 * 2
def baseEnd_6244303 : Nat := 3206328791311987869495479

theorem tailTrace_6244303 : CollatzResearch.WordTrace tailWord_6244303 prefixEnd_6244303 3206328791311987869495479 := by
  unfold tailWord_6244303
  simp only [CollatzResearch.WordTrace]
  refine ⟨227748440696964147893721563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151832293797976098595814375 227748440696964147893721563)
  ·
    refine ⟨341622661045446221840582345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227748440696964147893721563 341622661045446221840582345)
    ·
      refine ⟨256216995784084666380436759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341622661045446221840582345 256216995784084666380436759)
      ·
        refine ⟨384325493676126999570655139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256216995784084666380436759 384325493676126999570655139)
        ·
          refine ⟨576488240514190499355982709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384325493676126999570655139 576488240514190499355982709)
          ·
            refine ⟨54045772548205359314623379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 576488240514190499355982709 54045772548205359314623379)
            ·
              refine ⟨81068658822308038971935069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54045772548205359314623379 81068658822308038971935069)
              ·
                refine ⟨30400747058365514614475651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81068658822308038971935069 30400747058365514614475651)
                ·
                  refine ⟨45601120587548271921713477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30400747058365514614475651 45601120587548271921713477)
                  ·
                    refine ⟨8550210110165300985321277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45601120587548271921713477 8550210110165300985321277)
                    ·
                      refine ⟨3206328791311987869495479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8550210110165300985321277 3206328791311987869495479)
                      ·
                        rfl

theorem cell23_6244303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_6244303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244303 prefixEnd_6244303 := by exact prefixLift 6244303
  have htrace : WordTrace (prefixWord ++ tailWord_6244303) baseStart_6244303 baseEnd_6244303 := by
    simpa [prefixWord, tailWord_6244303, baseEnd_6244303] using wordTrace_append hprefix tailTrace_6244303
  have hstable : (prefixWord ++ tailWord_6244303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244303).length < 2 ^ (prefixWord ++ tailWord_6244303).sum := by decide
  have hdescent : baseEnd_6244303 < baseStart_6244303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244317 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_6244317 : Nat := 118140960795 + 6244317 * 2 ^ 59
def prefixEnd_6244317 : Nat := 4983230072969 + 3 ^ 40 * 6244317 * 2
def baseEnd_6244317 : Nat := 3206335980041150814720415

theorem tailTrace_6244317 : CollatzResearch.WordTrace tailWord_6244317 prefixEnd_6244317 3206335980041150814720415 := by
  unfold tailWord_6244317
  simp only [CollatzResearch.WordTrace]
  refine ⟨227748951318913428284731205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151832634212608952189820803 227748951318913428284731205)
  ·
    refine ⟨42702928372296267803387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227748951318913428284731205 42702928372296267803387101)
    ·
      refine ⟨16013598139611100426270163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42702928372296267803387101 16013598139611100426270163)
      ·
        refine ⟨24020397209416650639405245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013598139611100426270163 24020397209416650639405245)
        ·
          refine ⟨9007648953531243989776967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24020397209416650639405245 9007648953531243989776967)
          ·
            refine ⟨13511473430296865984665451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007648953531243989776967 13511473430296865984665451)
            ·
              refine ⟨20267210145445298976998177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13511473430296865984665451 20267210145445298976998177)
              ·
                refine ⟨15200407609083974232748633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20267210145445298976998177 15200407609083974232748633)
                ·
                  refine ⟨11400305706812980674561475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15200407609083974232748633 11400305706812980674561475)
                  ·
                    refine ⟨17100458560219471011842213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11400305706812980674561475 17100458560219471011842213)
                    ·
                      refine ⟨3206335980041150814720415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17100458560219471011842213 3206335980041150814720415)
                      ·
                        rfl

theorem cell23_6244317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_6244317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244317 prefixEnd_6244317 := by exact prefixLift 6244317
  have htrace : WordTrace (prefixWord ++ tailWord_6244317) baseStart_6244317 baseEnd_6244317 := by
    simpa [prefixWord, tailWord_6244317, baseEnd_6244317] using wordTrace_append hprefix tailTrace_6244317
  have hstable : (prefixWord ++ tailWord_6244317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244317).length < 2 ^ (prefixWord ++ tailWord_6244317).sum := by decide
  have hdescent : baseEnd_6244317 < baseStart_6244317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244323 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 8]
def baseStart_6244323 : Nat := 118140960795 + 6244323 * 2 ^ 59
def prefixEnd_6244323 : Nat := 4983230072969 + 3 ^ 40 * 6244323 * 2
def baseEnd_6244323 : Nat := 356259895658341976805043

theorem tailTrace_6244323 : CollatzResearch.WordTrace tailWord_6244323 prefixEnd_6244323 356259895658341976805043 := by
  unfold tailWord_6244323
  simp only [CollatzResearch.WordTrace]
  refine ⟨227749170156891691309449623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151832780104594460872966415 227749170156891691309449623)
  ·
    refine ⟨341623755235337536964174435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227749170156891691309449623 341623755235337536964174435)
    ·
      refine ⟨512435632853006305446261653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341623755235337536964174435 512435632853006305446261653)
      ·
        refine ⟨24020420289984670567793515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 512435632853006305446261653 24020420289984670567793515)
        ·
          refine ⟨36030630434977005851690273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24020420289984670567793515 36030630434977005851690273)
          ·
            refine ⟨27022972826232754388767705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36030630434977005851690273 27022972826232754388767705)
            ·
              refine ⟨20267229619674565791575779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27022972826232754388767705 20267229619674565791575779)
              ·
                refine ⟨30400844429511848687363669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20267229619674565791575779 30400844429511848687363669)
                ·
                  refine ⟨356259895658341976805043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30400844429511848687363669 356259895658341976805043)
                  ·
                    rfl

theorem cell23_6244323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 8].length) (baseStart_6244323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244323 prefixEnd_6244323 := by exact prefixLift 6244323
  have htrace : WordTrace (prefixWord ++ tailWord_6244323) baseStart_6244323 baseEnd_6244323 := by
    simpa [prefixWord, tailWord_6244323, baseEnd_6244323] using wordTrace_append hprefix tailTrace_6244323
  have hstable : (prefixWord ++ tailWord_6244323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244323).length < 2 ^ (prefixWord ++ tailWord_6244323).sum := by decide
  have hdescent : baseEnd_6244323 < baseStart_6244323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244383 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 6]
def baseStart_6244383 : Nat := 118140960795 + 6244383 * 2 ^ 59
def prefixEnd_6244383 : Nat := 4983230072969 + 3 ^ 40 * 6244383 * 2
def baseEnd_6244383 : Nat := 1068789956588115852165037

theorem tailTrace_6244383 : CollatzResearch.WordTrace tailWord_6244383 prefixEnd_6244383 1068789956588115852165037 := by
  unfold tailWord_6244383
  simp only [CollatzResearch.WordTrace]
  refine ⟨227751358536674321556633803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151834239024449547704422535 227751358536674321556633803)
  ·
    refine ⟨341627037805011482334950705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227751358536674321556633803 341627037805011482334950705)
    ·
      refine ⟨256220278353758611751213029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341627037805011482334950705 256220278353758611751213029)
      ·
        refine ⟨48041302191329739703352443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256220278353758611751213029 48041302191329739703352443)
        ·
          refine ⟨72061953286994609555028665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48041302191329739703352443 72061953286994609555028665)
          ·
            refine ⟨54046464965245957166271499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72061953286994609555028665 54046464965245957166271499)
            ·
              refine ⟨81069697447868935749407249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54046464965245957166271499 81069697447868935749407249)
              ·
                refine ⟨60802273085901701812055437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81069697447868935749407249 60802273085901701812055437)
                ·
                  refine ⟨22800852407213138179520789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60802273085901701812055437 22800852407213138179520789)
                  ·
                    refine ⟨1068789956588115852165037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22800852407213138179520789 1068789956588115852165037)
                    ·
                      rfl

theorem cell23_6244383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_6244383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244383 prefixEnd_6244383 := by exact prefixLift 6244383
  have htrace : WordTrace (prefixWord ++ tailWord_6244383) baseStart_6244383 baseEnd_6244383 := by
    simpa [prefixWord, tailWord_6244383, baseEnd_6244383] using wordTrace_append hprefix tailTrace_6244383
  have hstable : (prefixWord ++ tailWord_6244383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244383).length < 2 ^ (prefixWord ++ tailWord_6244383).sum := by decide
  have hdescent : baseEnd_6244383 < baseStart_6244383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244400 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_6244400 : Nat := 118140960795 + 6244400 * 2 ^ 59
def prefixEnd_6244400 : Nat := 4983230072969 + 3 ^ 40 * 6244400 * 2
def baseEnd_6244400 : Nat := 1068792866311824663327511

theorem tailTrace_6244400 : CollatzResearch.WordTrace tailWord_6244400 prefixEnd_6244400 1068792866311824663327511 := by
  unfold tailWord_6244400
  simp only [CollatzResearch.WordTrace]
  refine ⟨113875989288806366730001327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151834652385075155640001769 113875989288806366730001327)
  ·
    refine ⟨170813983933209550095001991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113875989288806366730001327 170813983933209550095001991)
    ·
      refine ⟨256220975899814325142502987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170813983933209550095001991 256220975899814325142502987)
      ·
        refine ⟨384331463849721487713754481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256220975899814325142502987 384331463849721487713754481)
        ·
          refine ⟨288248597887291115785315861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384331463849721487713754481 288248597887291115785315861)
          ·
            refine ⟨13511653025966771052436681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288248597887291115785315861 13511653025966771052436681)
            ·
              refine ⟨10133739769475078289327511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13511653025966771052436681 10133739769475078289327511)
              ·
                refine ⟨15200609654212617433991267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133739769475078289327511 15200609654212617433991267)
                ·
                  refine ⟨22800914481318926150986901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15200609654212617433991267 22800914481318926150986901)
                  ·
                    refine ⟨1068792866311824663327511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22800914481318926150986901 1068792866311824663327511)
                    ·
                      rfl

theorem cell23_6244400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_6244400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244400 prefixEnd_6244400 := by exact prefixLift 6244400
  have htrace : WordTrace (prefixWord ++ tailWord_6244400) baseStart_6244400 baseEnd_6244400 := by
    simpa [prefixWord, tailWord_6244400, baseEnd_6244400] using wordTrace_append hprefix tailTrace_6244400
  have hstable : (prefixWord ++ tailWord_6244400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244400).length < 2 ^ (prefixWord ++ tailWord_6244400).sum := by decide
  have hdescent : baseEnd_6244400 < baseStart_6244400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244403 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_6244403 : Nat := 118140960795 + 6244403 * 2 ^ 59
def prefixEnd_6244403 : Nat := 4983230072969 + 3 ^ 40 * 6244403 * 2
def baseEnd_6244403 : Nat := 3206380139377437478245019

theorem tailTrace_6244403 : CollatzResearch.WordTrace tailWord_6244403 prefixEnd_6244403 3206380139377437478245019 := by
  unfold tailWord_6244403
  simp only [CollatzResearch.WordTrace]
  refine ⟨227752087996601864972361863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151834725331067909981574575 227752087996601864972361863)
  ·
    refine ⟨341628131994902797458542795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227752087996601864972361863 341628131994902797458542795)
    ·
      refine ⟨512442197992354196187814193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341628131994902797458542795 512442197992354196187814193)
      ·
        refine ⟨384331648494265647140860645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512442197992354196187814193 384331648494265647140860645)
        ·
          refine ⟨72062184092674808838911371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384331648494265647140860645 72062184092674808838911371)
          ·
            refine ⟨108093276139012213258367057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72062184092674808838911371 108093276139012213258367057)
            ·
              refine ⟨81069957104259159943775293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108093276139012213258367057 81069957104259159943775293)
              ·
                refine ⟨30401233914097184978915735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81069957104259159943775293 30401233914097184978915735)
                ·
                  refine ⟨45601850871145777468373603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30401233914097184978915735 45601850871145777468373603)
                  ·
                    refine ⟨68402776306718666202560405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45601850871145777468373603 68402776306718666202560405)
                    ·
                      refine ⟨3206380139377437478245019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68402776306718666202560405 3206380139377437478245019)
                      ·
                        rfl

theorem cell23_6244403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_6244403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244403 prefixEnd_6244403 := by exact prefixLift 6244403
  have htrace : WordTrace (prefixWord ++ tailWord_6244403) baseStart_6244403 baseEnd_6244403 := by
    simpa [prefixWord, tailWord_6244403, baseEnd_6244403] using wordTrace_append hprefix tailTrace_6244403
  have hstable : (prefixWord ++ tailWord_6244403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244403).length < 2 ^ (prefixWord ++ tailWord_6244403).sum := by decide
  have hdescent : baseEnd_6244403 < baseStart_6244403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244407 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_6244407 : Nat := 118140960795 + 6244407 * 2 ^ 59
def prefixEnd_6244407 : Nat := 4983230072969 + 3 ^ 40 * 6244407 * 2
def baseEnd_6244407 : Nat := 3206382193300055462595001

theorem tailTrace_6244407 : CollatzResearch.WordTrace tailWord_6244407 prefixEnd_6244407 3206382193300055462595001 := by
  unfold tailWord_6244407
  simp only [CollatzResearch.WordTrace]
  refine ⟨227752233888587373655507475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151834822592391582437004983 227752233888587373655507475)
  ·
    refine ⟨341628350832881060483261213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227752233888587373655507475 341628350832881060483261213)
    ·
      refine ⟨128110631562330397681222955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341628350832881060483261213 128110631562330397681222955)
      ·
        refine ⟨192165947343495596521834433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128110631562330397681222955 192165947343495596521834433)
        ·
          refine ⟨144124460507621697391375825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192165947343495596521834433 144124460507621697391375825)
          ·
            refine ⟨108093345380716273043531869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144124460507621697391375825 108093345380716273043531869)
            ·
              refine ⟨40535004517768602391324451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108093345380716273043531869 40535004517768602391324451)
              ·
                refine ⟨60802506776652903586986677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40535004517768602391324451 60802506776652903586986677)
                ·
                  refine ⟨5700235010311209711280001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60802506776652903586986677 5700235010311209711280001)
                  ·
                    refine ⟨4275176257733407283460001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700235010311209711280001 4275176257733407283460001)
                    ·
                      refine ⟨3206382193300055462595001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275176257733407283460001 3206382193300055462595001)
                      ·
                        rfl

theorem cell23_6244407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_6244407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244407 prefixEnd_6244407 := by exact prefixLift 6244407
  have htrace : WordTrace (prefixWord ++ tailWord_6244407) baseStart_6244407 baseEnd_6244407 := by
    simpa [prefixWord, tailWord_6244407, baseEnd_6244407] using wordTrace_append hprefix tailTrace_6244407
  have hstable : (prefixWord ++ tailWord_6244407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244407).length < 2 ^ (prefixWord ++ tailWord_6244407).sum := by decide
  have hdescent : baseEnd_6244407 < baseStart_6244407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244433 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_6244433 : Nat := 118140960795 + 6244433 * 2 ^ 59
def prefixEnd_6244433 : Nat := 4983230072969 + 3 ^ 40 * 6244433 * 2
def baseEnd_6244433 : Nat := 3206395543797072360869881

theorem tailTrace_6244433 : CollatzResearch.WordTrace tailWord_6244433 prefixEnd_6244433 3206395543797072360869881 := by
  unfold tailWord_6244433
  simp only [CollatzResearch.WordTrace]
  refine ⟨227753182186493180095953953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151835454790995453397302635 227753182186493180095953953)
  ·
    refine ⟨170814886639869885071965465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227753182186493180095953953 170814886639869885071965465)
    ·
      refine ⟨128111164979902413803974099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170814886639869885071965465 128111164979902413803974099)
      ·
        refine ⟨192166747469853620705961149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128111164979902413803974099 192166747469853620705961149)
        ·
          refine ⟨72062530301195107764735431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192166747469853620705961149 72062530301195107764735431)
          ·
            refine ⟨108093795451792661647103147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72062530301195107764735431 108093795451792661647103147)
            ·
              refine ⟨162140693177688992470654721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108093795451792661647103147 162140693177688992470654721)
              ·
                refine ⟨121605519883266744352991041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162140693177688992470654721 121605519883266744352991041)
                ·
                  refine ⟨91204139912450058264743281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121605519883266744352991041 91204139912450058264743281)
                  ·
                    refine ⟨68403104934337543698557461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91204139912450058264743281 68403104934337543698557461)
                    ·
                      refine ⟨3206395543797072360869881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68403104934337543698557461 3206395543797072360869881)
                      ·
                        rfl

theorem cell23_6244433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_6244433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244433 prefixEnd_6244433 := by exact prefixLift 6244433
  have htrace : WordTrace (prefixWord ++ tailWord_6244433) baseStart_6244433 baseEnd_6244433 := by
    simpa [prefixWord, tailWord_6244433, baseEnd_6244433] using wordTrace_append hprefix tailTrace_6244433
  have hstable : (prefixWord ++ tailWord_6244433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244433).length < 2 ^ (prefixWord ++ tailWord_6244433).sum := by decide
  have hdescent : baseEnd_6244433 < baseStart_6244433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244484 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_6244484 : Nat := 118140960795 + 6244484 * 2 ^ 59
def prefixEnd_6244484 : Nat := 4983230072969 + 3 ^ 40 * 6244484 * 2
def baseEnd_6244484 : Nat := 3206421731310451661332147

theorem tailTrace_6244484 : CollatzResearch.WordTrace tailWord_6244484 prefixEnd_6244484 3206421731310451661332147 := by
  unfold tailWord_6244484
  simp only [CollatzResearch.WordTrace]
  refine ⟨113877521154654207903030253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151836694872872277204040337 113877521154654207903030253)
  ·
    refine ⟨42704070432995327963636345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113877521154654207903030253 42704070432995327963636345)
    ·
      refine ⟨32028052824746495972727259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42704070432995327963636345 32028052824746495972727259)
      ·
        refine ⟨48042079237119743959090889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32028052824746495972727259 48042079237119743959090889)
        ·
          refine ⟨36031559427839807969318167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48042079237119743959090889 36031559427839807969318167)
          ·
            refine ⟨54047339141759711953977251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36031559427839807969318167 54047339141759711953977251)
            ·
              refine ⟨81071008712639567930965877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54047339141759711953977251 81071008712639567930965877)
              ·
                refine ⟨7600407066809959493528051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81071008712639567930965877 7600407066809959493528051)
                ·
                  refine ⟨11400610600214939240292077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600407066809959493528051 11400610600214939240292077)
                  ·
                    refine ⟨4275228975080602215109529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11400610600214939240292077 4275228975080602215109529)
                    ·
                      refine ⟨3206421731310451661332147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275228975080602215109529 3206421731310451661332147)
                      ·
                        rfl

theorem cell23_6244484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_6244484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244484 prefixEnd_6244484 := by exact prefixLift 6244484
  have htrace : WordTrace (prefixWord ++ tailWord_6244484) baseStart_6244484 baseEnd_6244484 := by
    simpa [prefixWord, tailWord_6244484, baseEnd_6244484] using wordTrace_append hprefix tailTrace_6244484
  have hstable : (prefixWord ++ tailWord_6244484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244484).length < 2 ^ (prefixWord ++ tailWord_6244484).sum := by decide
  have hdescent : baseEnd_6244484 < baseStart_6244484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244537 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 5]
def baseStart_6244537 : Nat := 118140960795 + 6244537 * 2 ^ 59
def prefixEnd_6244537 : Nat := 4983230072969 + 3 ^ 40 * 6244537 * 2
def baseEnd_6244537 : Nat := 356272105087237772663267

theorem tailTrace_6244537 : CollatzResearch.WordTrace tailWord_6244537 prefixEnd_6244537 356272105087237772663267 := by
  unfold tailWord_6244537
  simp only [CollatzResearch.WordTrace]
  refine ⟨227756975378116405857739865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151837983585410937238493243 227756975378116405857739865)
  ·
    refine ⟨170817731533587304393304899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227756975378116405857739865 170817731533587304393304899)
    ·
      refine ⟨256226597300380956589957349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170817731533587304393304899 256226597300380956589957349)
      ·
        refine ⟨48042486993821429360617003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256226597300380956589957349 48042486993821429360617003)
        ·
          refine ⟨72063730490732144040925505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48042486993821429360617003 72063730490732144040925505)
          ·
            refine ⟨54047797868049108030694129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72063730490732144040925505 54047797868049108030694129)
            ·
              refine ⟨40535848401036831023020597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54047797868049108030694129 40535848401036831023020597)
              ·
                refine ⟨3800235787597202908408181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40535848401036831023020597 3800235787597202908408181)
                ·
                  refine ⟨356272105087237772663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800235787597202908408181 356272105087237772663267)
                  ·
                    rfl

theorem cell23_6244537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 5].length) (baseStart_6244537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244537 prefixEnd_6244537 := by exact prefixLift 6244537
  have htrace : WordTrace (prefixWord ++ tailWord_6244537) baseStart_6244537 baseEnd_6244537 := by
    simpa [prefixWord, tailWord_6244537, baseEnd_6244537] using wordTrace_append hprefix tailTrace_6244537
  have hstable : (prefixWord ++ tailWord_6244537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244537).length < 2 ^ (prefixWord ++ tailWord_6244537).sum := by decide
  have hdescent : baseEnd_6244537 < baseStart_6244537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244548 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6244548 : Nat := 118140960795 + 6244548 * 2 ^ 59
def prefixEnd_6244548 : Nat := 4983230072969 + 3 ^ 40 * 6244548 * 2
def baseEnd_6244548 : Nat := 3206454594072339410931853

theorem tailTrace_6244548 : CollatzResearch.WordTrace tailWord_6244548 prefixEnd_6244548 3206454594072339410931853 := by
  unfold tailWord_6244548
  simp only [CollatzResearch.WordTrace]
  refine ⟨113878688290538277368195149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151838251054051036490926865 113878688290538277368195149)
  ·
    refine ⟨42704508108951854013073181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113878688290538277368195149 42704508108951854013073181)
    ·
      refine ⟨16014190540856945254902443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42704508108951854013073181 16014190540856945254902443)
      ·
        refine ⟨24021285811285417882353665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014190540856945254902443 24021285811285417882353665)
        ·
          refine ⟨18015964358464063411765249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24021285811285417882353665 18015964358464063411765249)
          ·
            refine ⟨13511973268848047558823937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18015964358464063411765249 13511973268848047558823937)
            ·
              refine ⟨10133979951636035669117953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13511973268848047558823937 10133979951636035669117953)
              ·
                refine ⟨7600484963727026751838465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10133979951636035669117953 7600484963727026751838465)
                ·
                  refine ⟨5700363722795270063878849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7600484963727026751838465 5700363722795270063878849)
                  ·
                    refine ⟨4275272792096452547909137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700363722795270063878849 4275272792096452547909137)
                    ·
                      refine ⟨3206454594072339410931853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275272792096452547909137 3206454594072339410931853)
                      ·
                        rfl

theorem cell23_6244548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6244548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244548 prefixEnd_6244548 := by exact prefixLift 6244548
  have htrace : WordTrace (prefixWord ++ tailWord_6244548) baseStart_6244548 baseEnd_6244548 := by
    simpa [prefixWord, tailWord_6244548, baseEnd_6244548] using wordTrace_append hprefix tailTrace_6244548
  have hstable : (prefixWord ++ tailWord_6244548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244548).length < 2 ^ (prefixWord ++ tailWord_6244548).sum := by decide
  have hdescent : baseEnd_6244548 < baseStart_6244548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244584 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_6244584 : Nat := 118140960795 + 6244584 * 2 ^ 59
def prefixEnd_6244584 : Nat := 4983230072969 + 3 ^ 40 * 6244584 * 2
def baseEnd_6244584 : Nat := 1068824359791967090027229

theorem tailTrace_6244584 : CollatzResearch.WordTrace tailWord_6244584 prefixEnd_6244584 1068824359791967090027229 := by
  unfold tailWord_6244584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113879344804473066442350403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151839126405964088589800537 113879344804473066442350403)
  ·
    refine ⟨170819017206709599663525605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113879344804473066442350403 170819017206709599663525605)
    ·
      refine ⟨32028565726258049936911051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170819017206709599663525605 32028565726258049936911051)
      ·
        refine ⟨48042848589387074905366577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32028565726258049936911051 48042848589387074905366577)
        ·
          refine ⟨36032136442040306179024933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48042848589387074905366577 36032136442040306179024933)
          ·
            refine ⟨6756025582882557408567175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36032136442040306179024933 6756025582882557408567175)
            ·
              refine ⟨10134038374323836112850763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756025582882557408567175 10134038374323836112850763)
              ·
                refine ⟨15201057561485754169276145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134038374323836112850763 15201057561485754169276145)
                ·
                  refine ⟨11400793171114315626957109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15201057561485754169276145 11400793171114315626957109)
                  ·
                    refine ⟨1068824359791967090027229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11400793171114315626957109 1068824359791967090027229)
                    ·
                      rfl

theorem cell23_6244584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_6244584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244584 prefixEnd_6244584 := by exact prefixLift 6244584
  have htrace : WordTrace (prefixWord ++ tailWord_6244584) baseStart_6244584 baseEnd_6244584 := by
    simpa [prefixWord, tailWord_6244584, baseEnd_6244584] using wordTrace_append hprefix tailTrace_6244584
  have hstable : (prefixWord ++ tailWord_6244584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244584).length < 2 ^ (prefixWord ++ tailWord_6244584).sum := by decide
  have hdescent : baseEnd_6244584 < baseStart_6244584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244587 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 6, 2]
def baseStart_6244587 : Nat := 118140960795 + 6244587 * 2 ^ 59
def prefixEnd_6244587 : Nat := 4983230072969 + 3 ^ 40 * 6244587 * 2
def baseEnd_6244587 : Nat := 3206474619817864758344173

theorem tailTrace_6244587 : CollatzResearch.WordTrace tailWord_6244587 prefixEnd_6244587 3206474619817864758344173 := by
  unfold tailWord_6244587
  simp only [CollatzResearch.WordTrace]
  refine ⟨227758799027935264397060015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151839199351956842931373343 227758799027935264397060015)
  ·
    refine ⟨341638198541902896595590023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227758799027935264397060015 341638198541902896595590023)
    ·
      refine ⟨512457297812854344893385035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341638198541902896595590023 512457297812854344893385035)
      ·
        refine ⟨768685946719281517340077553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512457297812854344893385035 768685946719281517340077553)
        ·
          refine ⟨576514460039461138005058165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768685946719281517340077553 576514460039461138005058165)
          ·
            refine ⟨54048230628699481687974203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 576514460039461138005058165 54048230628699481687974203)
            ·
              refine ⟨81072345943049222531961305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54048230628699481687974203 81072345943049222531961305)
              ·
                refine ⟨60804259457286916898970979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81072345943049222531961305 60804259457286916898970979)
                ·
                  refine ⟨91206389185930375348456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60804259457286916898970979 91206389185930375348456469)
                  ·
                    refine ⟨4275299493090486344458897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91206389185930375348456469 4275299493090486344458897)
                    ·
                      refine ⟨3206474619817864758344173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275299493090486344458897 3206474619817864758344173)
                      ·
                        rfl

theorem cell23_6244587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6, 2].length) (baseStart_6244587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244587 prefixEnd_6244587 := by exact prefixLift 6244587
  have htrace : WordTrace (prefixWord ++ tailWord_6244587) baseStart_6244587 baseEnd_6244587 := by
    simpa [prefixWord, tailWord_6244587, baseEnd_6244587] using wordTrace_append hprefix tailTrace_6244587
  have hstable : (prefixWord ++ tailWord_6244587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244587).length < 2 ^ (prefixWord ++ tailWord_6244587).sum := by decide
  have hdescent : baseEnd_6244587 < baseStart_6244587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244600 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_6244600 : Nat := 118140960795 + 6244600 * 2 ^ 59
def prefixEnd_6244600 : Nat := 4983230072969 + 3 ^ 40 * 6244600 * 2
def baseEnd_6244600 : Nat := 3206481295066373207481613

theorem tailTrace_6244600 : CollatzResearch.WordTrace tailWord_6244600 prefixEnd_6244600 3206481295066373207481613 := by
  unfold tailWord_6244600
  simp only [CollatzResearch.WordTrace]
  refine ⟨113879636588444083808641627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151839515451258778411522169 113879636588444083808641627)
  ·
    refine ⟨170819454882666125712962441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113879636588444083808641627 170819454882666125712962441)
    ·
      refine ⟨128114591161999594284721831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170819454882666125712962441 128114591161999594284721831)
      ·
        refine ⟨192171886742999391427082747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128114591161999594284721831 192171886742999391427082747)
        ·
          refine ⟨288257830114499087140624121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192171886742999391427082747 288257830114499087140624121)
          ·
            refine ⟨216193372585874315355468091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288257830114499087140624121 216193372585874315355468091)
            ·
              refine ⟨324290058878811473033202137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216193372585874315355468091 324290058878811473033202137)
              ·
                refine ⟨243217544159108604774901603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324290058878811473033202137 243217544159108604774901603)
                ·
                  refine ⟨364826316238662907162352405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243217544159108604774901603 364826316238662907162352405)
                  ·
                    refine ⟨17101233573687323773235269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 364826316238662907162352405 17101233573687323773235269)
                    ·
                      refine ⟨3206481295066373207481613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17101233573687323773235269 3206481295066373207481613)
                      ·
                        rfl

theorem cell23_6244600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_6244600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244600 prefixEnd_6244600 := by exact prefixLift 6244600
  have htrace : WordTrace (prefixWord ++ tailWord_6244600) baseStart_6244600 baseEnd_6244600 := by
    simpa [prefixWord, tailWord_6244600, baseEnd_6244600] using wordTrace_append hprefix tailTrace_6244600
  have hstable : (prefixWord ++ tailWord_6244600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244600).length < 2 ^ (prefixWord ++ tailWord_6244600).sum := by decide
  have hdescent : baseEnd_6244600 < baseStart_6244600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244604 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_6244604 : Nat := 118140960795 + 6244604 * 2 ^ 59
def prefixEnd_6244604 : Nat := 4983230072969 + 3 ^ 40 * 6244604 * 2
def baseEnd_6244604 : Nat := 3206483348988991191831595

theorem tailTrace_6244604 : CollatzResearch.WordTrace tailWord_6244604 prefixEnd_6244604 3206483348988991191831595 := by
  unfold tailWord_6244604
  simp only [CollatzResearch.WordTrace]
  refine ⟨113879709534436838150214433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151839612712582450866952577 113879709534436838150214433)
  ·
    refine ⟨85409782150827628612660825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113879709534436838150214433 85409782150827628612660825)
    ·
      refine ⟨64057336613120721459495619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85409782150827628612660825 64057336613120721459495619)
      ·
        refine ⟨96086004919681082189243429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64057336613120721459495619 96086004919681082189243429)
        ·
          refine ⟨18016125922440202910483143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96086004919681082189243429 18016125922440202910483143)
          ·
            refine ⟨27024188883660304365724715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18016125922440202910483143 27024188883660304365724715)
            ·
              refine ⟨40536283325490456548587073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27024188883660304365724715 40536283325490456548587073)
              ·
                refine ⟨30402212494117842411440305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40536283325490456548587073 30402212494117842411440305)
                ·
                  refine ⟨22801659370588381808580229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30402212494117842411440305 22801659370588381808580229)
                  ·
                    refine ⟨4275311131985321589108793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22801659370588381808580229 4275311131985321589108793)
                    ·
                      refine ⟨3206483348988991191831595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275311131985321589108793 3206483348988991191831595)
                      ·
                        rfl

theorem cell23_6244604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_6244604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244604 prefixEnd_6244604 := by exact prefixLift 6244604
  have htrace : WordTrace (prefixWord ++ tailWord_6244604) baseStart_6244604 baseEnd_6244604 := by
    simpa [prefixWord, tailWord_6244604, baseEnd_6244604] using wordTrace_append hprefix tailTrace_6244604
  have hstable : (prefixWord ++ tailWord_6244604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244604).length < 2 ^ (prefixWord ++ tailWord_6244604).sum := by decide
  have hdescent : baseEnd_6244604 < baseStart_6244604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244607 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_6244607 : Nat := 118140960795 + 6244607 * 2 ^ 59
def prefixEnd_6244607 : Nat := 4983230072969 + 3 ^ 40 * 6244607 * 2
def baseEnd_6244607 : Nat := 3206484889430954680094081

theorem tailTrace_6244607 : CollatzResearch.WordTrace tailWord_6244607 prefixEnd_6244607 3206484889430954680094081 := by
  unfold tailWord_6244607
  simp only [CollatzResearch.WordTrace]
  refine ⟨227759528487862807812788075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151839685658575205208525383 227759528487862807812788075)
  ·
    refine ⟨341639292731794211719182113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227759528487862807812788075 341639292731794211719182113)
    ·
      refine ⟨256229469548845658789386585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341639292731794211719182113 256229469548845658789386585)
      ·
        refine ⟨192172102161634244092039939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256229469548845658789386585 192172102161634244092039939)
        ·
          refine ⟨288258153242451366138059909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192172102161634244092039939 288258153242451366138059909)
          ·
            refine ⟨54048403732959631150886233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288258153242451366138059909 54048403732959631150886233)
            ·
              refine ⟨40536302799719723363164675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54048403732959631150886233 40536302799719723363164675)
              ·
                refine ⟨60804454199579585044747013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40536302799719723363164675 60804454199579585044747013)
                ·
                  refine ⟨11400835162421172195890065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60804454199579585044747013 11400835162421172195890065)
                  ·
                    refine ⟨8550626371815879146917549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11400835162421172195890065 8550626371815879146917549)
                    ·
                      refine ⟨3206484889430954680094081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8550626371815879146917549 3206484889430954680094081)
                      ·
                        rfl

theorem cell23_6244607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_6244607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244607 prefixEnd_6244607 := by exact prefixLift 6244607
  have htrace : WordTrace (prefixWord ++ tailWord_6244607) baseStart_6244607 baseEnd_6244607 := by
    simpa [prefixWord, tailWord_6244607, baseEnd_6244607] using wordTrace_append hprefix tailTrace_6244607
  have hstable : (prefixWord ++ tailWord_6244607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244607).length < 2 ^ (prefixWord ++ tailWord_6244607).sum := by decide
  have hdescent : baseEnd_6244607 < baseStart_6244607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244664 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_6244664 : Nat := 118140960795 + 6244664 * 2 ^ 59
def prefixEnd_6244664 : Nat := 4983230072969 + 3 ^ 40 * 6244664 * 2
def baseEnd_6244664 : Nat := 3206514157828260957081319

theorem tailTrace_6244664 : CollatzResearch.WordTrace tailWord_6244664 prefixEnd_6244664 3206514157828260957081319 := by
  unfold tailWord_6244664
  simp only [CollatzResearch.WordTrace]
  refine ⟨113880803724328153273806523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151841071632437537698408697 113880803724328153273806523)
  ·
    refine ⟨170821205586492229910709785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113880803724328153273806523 170821205586492229910709785)
    ·
      refine ⟨128115904189869172433032339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170821205586492229910709785 128115904189869172433032339)
      ·
        refine ⟨192173856284803758649548509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128115904189869172433032339 192173856284803758649548509)
        ·
          refine ⟨72065196106801409493580691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192173856284803758649548509 72065196106801409493580691)
          ·
            refine ⟨108097794160202114240371037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72065196106801409493580691 108097794160202114240371037)
            ·
              refine ⟨40536672810075792840139139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108097794160202114240371037 40536672810075792840139139)
              ·
                refine ⟨60805009215113689260208709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40536672810075792840139139 60805009215113689260208709)
                ·
                  refine ⟨11400939227833816736289133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60805009215113689260208709 11400939227833816736289133)
                  ·
                    refine ⟨4275352210437681276108425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11400939227833816736289133 4275352210437681276108425)
                    ·
                      refine ⟨3206514157828260957081319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275352210437681276108425 3206514157828260957081319)
                      ·
                        rfl

theorem cell23_6244664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_6244664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244664 prefixEnd_6244664 := by exact prefixLift 6244664
  have htrace : WordTrace (prefixWord ++ tailWord_6244664) baseStart_6244664 baseEnd_6244664 := by
    simpa [prefixWord, tailWord_6244664, baseEnd_6244664] using wordTrace_append hprefix tailTrace_6244664
  have hstable : (prefixWord ++ tailWord_6244664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244664).length < 2 ^ (prefixWord ++ tailWord_6244664).sum := by decide
  have hdescent : baseEnd_6244664 < baseStart_6244664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244687 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 6, 4]
def baseStart_6244687 : Nat := 118140960795 + 6244687 * 2 ^ 59
def prefixEnd_6244687 : Nat := 4983230072969 + 3 ^ 40 * 6244687 * 2
def baseEnd_6244687 : Nat := 1068841989294438122364571

theorem tailTrace_6244687 : CollatzResearch.WordTrace tailWord_6244687 prefixEnd_6244687 1068841989294438122364571 := by
  unfold tailWord_6244687
  simp only [CollatzResearch.WordTrace]
  refine ⟨227762446327572981475700315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151841630885048654317133543 227762446327572981475700315)
  ·
    refine ⟨341643669491359472213550473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227762446327572981475700315 341643669491359472213550473)
    ·
      refine ⟨256232752118519604160162855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341643669491359472213550473 256232752118519604160162855)
      ·
        refine ⟨384349128177779406240244283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256232752118519604160162855 384349128177779406240244283)
        ·
          refine ⟨576523692266669109360366425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384349128177779406240244283 576523692266669109360366425)
          ·
            refine ⟨432392769200001832020274819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576523692266669109360366425 432392769200001832020274819)
            ·
              refine ⟨648589153800002748030412229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432392769200001832020274819 648589153800002748030412229)
              ·
                refine ⟨121610466337500515255702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648589153800002748030412229 121610466337500515255702293)
                ·
                  refine ⟨5700490609570336652611045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121610466337500515255702293 5700490609570336652611045)
                  ·
                    refine ⟨1068841989294438122364571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700490609570336652611045 1068841989294438122364571)
                    ·
                      rfl

theorem cell23_6244687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_6244687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244687 prefixEnd_6244687 := by exact prefixLift 6244687
  have htrace : WordTrace (prefixWord ++ tailWord_6244687) baseStart_6244687 baseEnd_6244687 := by
    simpa [prefixWord, tailWord_6244687, baseEnd_6244687] using wordTrace_append hprefix tailTrace_6244687
  have hstable : (prefixWord ++ tailWord_6244687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244687).length < 2 ^ (prefixWord ++ tailWord_6244687).sum := by decide
  have hdescent : baseEnd_6244687 < baseStart_6244687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244704 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_6244704 : Nat := 118140960795 + 6244704 * 2 ^ 59
def prefixEnd_6244704 : Nat := 4983230072969 + 3 ^ 40 * 6244704 * 2
def baseEnd_6244704 : Nat := 1068844899018146933527045

theorem tailTrace_6244704 : CollatzResearch.WordTrace tailWord_6244704 prefixEnd_6244704 1068844899018146933527045 := by
  unfold tailWord_6244704
  simp only [CollatzResearch.WordTrace]
  refine ⟨113881533184255696689534583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151842044245674262252712777 113881533184255696689534583)
  ·
    refine ⟨170822299776383545034301875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113881533184255696689534583 170822299776383545034301875)
    ·
      refine ⟨256233449664575317551452813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170822299776383545034301875 256233449664575317551452813)
      ·
        refine ⟨96087543624215744081794805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256233449664575317551452813 96087543624215744081794805)
        ·
          refine ⟨9008207214770226007668263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96087543624215744081794805 9008207214770226007668263)
          ·
            refine ⟨13512310822155339011502395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008207214770226007668263 13512310822155339011502395)
            ·
              refine ⟨20268466233233008517253593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13512310822155339011502395 20268466233233008517253593)
              ·
                refine ⟨15201349674924756387940195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20268466233233008517253593 15201349674924756387940195)
                ·
                  refine ⟨22802024512387134581910293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15201349674924756387940195 22802024512387134581910293)
                  ·
                    refine ⟨1068844899018146933527045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22802024512387134581910293 1068844899018146933527045)
                    ·
                      rfl

theorem cell23_6244704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_6244704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244704 prefixEnd_6244704 := by exact prefixLift 6244704
  have htrace : WordTrace (prefixWord ++ tailWord_6244704) baseStart_6244704 baseEnd_6244704 := by
    simpa [prefixWord, tailWord_6244704, baseEnd_6244704] using wordTrace_append hprefix tailTrace_6244704
  have hstable : (prefixWord ++ tailWord_6244704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244704).length < 2 ^ (prefixWord ++ tailWord_6244704).sum := by decide
  have hdescent : baseEnd_6244704 < baseStart_6244704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244738 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6244738 : Nat := 118140960795 + 6244738 * 2 ^ 59
def prefixEnd_6244738 : Nat := 4983230072969 + 3 ^ 40 * 6244738 * 2
def baseEnd_6244738 : Nat := 1068850718465564555851993

theorem tailTrace_6244738 : CollatzResearch.WordTrace tailWord_6244738 prefixEnd_6244738 1068850718465564555851993 := by
  unfold tailWord_6244738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56941076612597054296451717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151842870966925478123871245 56941076612597054296451717)
  ·
    refine ⟨10676451864861947680584697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56941076612597054296451717 10676451864861947680584697)
    ·
      refine ⟨8007338898646460760438523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10676451864861947680584697 8007338898646460760438523)
      ·
        refine ⟨12011008347969691140657785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007338898646460760438523 12011008347969691140657785)
        ·
          refine ⟨9008256260977268355493339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12011008347969691140657785 9008256260977268355493339)
          ·
            refine ⟨13512384391465902533240009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008256260977268355493339 13512384391465902533240009)
            ·
              refine ⟨10134288293599426899930007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13512384391465902533240009 10134288293599426899930007)
              ·
                refine ⟨15201432440399140349895011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134288293599426899930007 15201432440399140349895011)
                ·
                  refine ⟨22802148660598710524842517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15201432440399140349895011 22802148660598710524842517)
                  ·
                    refine ⟨1068850718465564555851993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22802148660598710524842517 1068850718465564555851993)
                    ·
                      rfl

theorem cell23_6244738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6244738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244738 prefixEnd_6244738 := by exact prefixLift 6244738
  have htrace : WordTrace (prefixWord ++ tailWord_6244738) baseStart_6244738 baseEnd_6244738 := by
    simpa [prefixWord, tailWord_6244738, baseEnd_6244738] using wordTrace_append hprefix tailTrace_6244738
  have hstable : (prefixWord ++ tailWord_6244738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244738).length < 2 ^ (prefixWord ++ tailWord_6244738).sum := by decide
  have hdescent : baseEnd_6244738 < baseStart_6244738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244757 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6244757 : Nat := 118140960795 + 6244757 * 2 ^ 59
def prefixEnd_6244757 : Nat := 4983230072969 + 3 ^ 40 * 6244757 * 2
def baseEnd_6244757 : Nat := 3206561911529129093218391

theorem tailTrace_6244757 : CollatzResearch.WordTrace tailWord_6244757 prefixEnd_6244757 3206561911529129093218391 := by
  unfold tailWord_6244757
  simp only [CollatzResearch.WordTrace]
  refine ⟨227764999437319383430748525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151843332958212922287165683 227764999437319383430748525)
  ·
    refine ⟨85411874788994768786530697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227764999437319383430748525 85411874788994768786530697)
    ·
      refine ⟨64058906091746076589898023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85411874788994768786530697 64058906091746076589898023)
      ·
        refine ⟨96088359137619114884847035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64058906091746076589898023 96088359137619114884847035)
        ·
          refine ⟨144132538706428672327270553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96088359137619114884847035 144132538706428672327270553)
          ·
            refine ⟨108099404029821504245452915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144132538706428672327270553 108099404029821504245452915)
            ·
              refine ⟨162149106044732256368179373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108099404029821504245452915 162149106044732256368179373)
              ·
                refine ⟨60805914766774596138067265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162149106044732256368179373 60805914766774596138067265)
                ·
                  refine ⟨45604436075080947103550449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60805914766774596138067265 45604436075080947103550449)
                  ·
                    refine ⟨34203327056310710327662837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45604436075080947103550449 34203327056310710327662837)
                    ·
                      refine ⟨3206561911529129093218391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34203327056310710327662837 3206561911529129093218391)
                      ·
                        rfl

theorem cell23_6244757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6244757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244757 prefixEnd_6244757 := by exact prefixLift 6244757
  have htrace : WordTrace (prefixWord ++ tailWord_6244757) baseStart_6244757 baseEnd_6244757 := by
    simpa [prefixWord, tailWord_6244757, baseEnd_6244757] using wordTrace_append hprefix tailTrace_6244757
  have hstable : (prefixWord ++ tailWord_6244757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244757).length < 2 ^ (prefixWord ++ tailWord_6244757).sum := by decide
  have hdescent : baseEnd_6244757 < baseStart_6244757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244765 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_6244765 : Nat := 118140960795 + 6244765 * 2 ^ 59
def prefixEnd_6244765 : Nat := 4983230072969 + 3 ^ 40 * 6244765 * 2
def baseEnd_6244765 : Nat := 3206566019374365061918355

theorem tailTrace_6244765 : CollatzResearch.WordTrace tailWord_6244765 prefixEnd_6244765 3206566019374365061918355 := by
  unfold tailWord_6244765
  simp only [CollatzResearch.WordTrace]
  refine ⟨227765291221290400797039749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151843527480860267198026499 227765291221290400797039749)
  ·
    refine ⟨42705992103991950149444953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227765291221290400797039749 42705992103991950149444953)
    ·
      refine ⟨32029494077993962612083715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42705992103991950149444953 32029494077993962612083715)
      ·
        refine ⟨48044241116990943918125573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32029494077993962612083715 48044241116990943918125573)
        ·
          refine ⟨9008295209435801984648545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48044241116990943918125573 9008295209435801984648545)
          ·
            refine ⟨6756221407076851488486409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9008295209435801984648545 6756221407076851488486409)
            ·
              refine ⟨5067166055307638616364807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756221407076851488486409 5067166055307638616364807)
              ·
                refine ⟨7600749082961457924547211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067166055307638616364807 7600749082961457924547211)
                ·
                  refine ⟨11401123624442186886820817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600749082961457924547211 11401123624442186886820817)
                  ·
                    refine ⟨8550842718331640165115613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11401123624442186886820817 8550842718331640165115613)
                    ·
                      refine ⟨3206566019374365061918355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8550842718331640165115613 3206566019374365061918355)
                      ·
                        rfl

theorem cell23_6244765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_6244765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244765 prefixEnd_6244765 := by exact prefixLift 6244765
  have htrace : WordTrace (prefixWord ++ tailWord_6244765) baseStart_6244765 baseEnd_6244765 := by
    simpa [prefixWord, tailWord_6244765, baseEnd_6244765] using wordTrace_append hprefix tailTrace_6244765
  have hstable : (prefixWord ++ tailWord_6244765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244765).length < 2 ^ (prefixWord ++ tailWord_6244765).sum := by decide
  have hdescent : baseEnd_6244765 < baseStart_6244765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244787 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_6244787 : Nat := 118140960795 + 6244787 * 2 ^ 59
def prefixEnd_6244787 : Nat := 4983230072969 + 3 ^ 40 * 6244787 * 2
def baseEnd_6244787 : Nat := 3206577315948763975843253

theorem tailTrace_6244787 : CollatzResearch.WordTrace tailWord_6244787 prefixEnd_6244787 3206577315948763975843253 := by
  unfold tailWord_6244787
  simp only [CollatzResearch.WordTrace]
  refine ⟨227766093627210698554340615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151844062418140465702893743 227766093627210698554340615)
  ·
    refine ⟨341649140440816047831510923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227766093627210698554340615 341649140440816047831510923)
    ·
      refine ⟨512473710661224071747266385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341649140440816047831510923 512473710661224071747266385)
      ·
        refine ⟨384355282995918053810449789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512473710661224071747266385 384355282995918053810449789)
        ·
          refine ⟨144133231123469270178918671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384355282995918053810449789 144133231123469270178918671)
          ·
            refine ⟨216199846685203905268378007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144133231123469270178918671 216199846685203905268378007)
            ·
              refine ⟨324299770027805857902567011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216199846685203905268378007 324299770027805857902567011)
              ·
                refine ⟨486449655041708786853850517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324299770027805857902567011 486449655041708786853850517)
                ·
                  refine ⟨22802327580080099383774243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 486449655041708786853850517 22802327580080099383774243)
                  ·
                    refine ⟨34203491370120149075661365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22802327580080099383774243 34203491370120149075661365)
                    ·
                      refine ⟨3206577315948763975843253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34203491370120149075661365 3206577315948763975843253)
                      ·
                        rfl

theorem cell23_6244787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_6244787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244787 prefixEnd_6244787 := by exact prefixLift 6244787
  have htrace : WordTrace (prefixWord ++ tailWord_6244787) baseStart_6244787 baseEnd_6244787 := by
    simpa [prefixWord, tailWord_6244787, baseEnd_6244787] using wordTrace_append hprefix tailTrace_6244787
  have hstable : (prefixWord ++ tailWord_6244787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244787).length < 2 ^ (prefixWord ++ tailWord_6244787).sum := by decide
  have hdescent : baseEnd_6244787 < baseStart_6244787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244918 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6244918 : Nat := 118140960795 + 6244918 * 2 ^ 59
def prefixEnd_6244918 : Nat := 4983230072969 + 3 ^ 40 * 6244918 * 2
def baseEnd_6244918 : Nat := 1068881527304834321101717

theorem tailTrace_6244918 : CollatzResearch.WordTrace tailWord_6244918 prefixEnd_6244918 1068881527304834321101717 := by
  unfold tailWord_6244918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235679474358506745459963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151847247726490738618239605 14235679474358506745459963)
  ·
    refine ⟨21353519211537760118189945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14235679474358506745459963 21353519211537760118189945)
    ·
      refine ⟨16015139408653320088642459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21353519211537760118189945 16015139408653320088642459)
      ·
        refine ⟨24022709112979980132963689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16015139408653320088642459 24022709112979980132963689)
        ·
          refine ⟨18017031834734985099722767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24022709112979980132963689 18017031834734985099722767)
          ·
            refine ⟨27025547752102477649584151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18017031834734985099722767 27025547752102477649584151)
            ·
              refine ⟨40538321628153716474376227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27025547752102477649584151 40538321628153716474376227)
              ·
                refine ⟨60807482442230574711564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40538321628153716474376227 60807482442230574711564341)
                ·
                  refine ⟨5700701478959116379209157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60807482442230574711564341 5700701478959116379209157)
                  ·
                    refine ⟨1068881527304834321101717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700701478959116379209157 1068881527304834321101717)
                    ·
                      rfl

theorem cell23_6244918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6244918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244918 prefixEnd_6244918 := by exact prefixLift 6244918
  have htrace : WordTrace (prefixWord ++ tailWord_6244918) baseStart_6244918 baseEnd_6244918 := by
    simpa [prefixWord, tailWord_6244918, baseEnd_6244918] using wordTrace_append hprefix tailTrace_6244918
  have hstable : (prefixWord ++ tailWord_6244918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244918).length < 2 ^ (prefixWord ++ tailWord_6244918).sum := by decide
  have hdescent : baseEnd_6244918 < baseStart_6244918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244935 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 1, 4]
def baseStart_6244935 : Nat := 118140960795 + 6244935 * 2 ^ 59
def prefixEnd_6244935 : Nat := 4983230072969 + 3 ^ 40 * 6244935 * 2
def baseEnd_6244935 : Nat := 1068884437028543132264191

theorem tailTrace_6244935 : CollatzResearch.WordTrace tailWord_6244935 prefixEnd_6244935 1068884437028543132264191 := by
  unfold tailWord_6244935
  simp only [CollatzResearch.WordTrace]
  refine ⟨227771491630674519830728259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151847661087116346553818839 227771491630674519830728259)
  ·
    refine ⟨341657237446011779746092389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227771491630674519830728259 341657237446011779746092389)
    ·
      refine ⟨64060732021127208702392323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341657237446011779746092389 64060732021127208702392323)
      ·
        refine ⟨96091098031690813053588485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64060732021127208702392323 96091098031690813053588485)
        ·
          refine ⟨18017080880942027447547841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96091098031690813053588485 18017080880942027447547841)
          ·
            refine ⟨13512810660706520585660881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18017080880942027447547841 13512810660706520585660881)
            ·
              refine ⟨10134607995529890439245661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13512810660706520585660881 10134607995529890439245661)
              ·
                refine ⟨3800477998323708914717123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10134607995529890439245661 3800477998323708914717123)
                ·
                  refine ⟨5700716997485563372075685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800477998323708914717123 5700716997485563372075685)
                  ·
                    refine ⟨1068884437028543132264191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700716997485563372075685 1068884437028543132264191)
                    ·
                      rfl

theorem cell23_6244935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_6244935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244935 prefixEnd_6244935 := by exact prefixLift 6244935
  have htrace : WordTrace (prefixWord ++ tailWord_6244935) baseStart_6244935 baseEnd_6244935 := by
    simpa [prefixWord, tailWord_6244935, baseEnd_6244935] using wordTrace_append hprefix tailTrace_6244935
  have hstable : (prefixWord ++ tailWord_6244935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244935).length < 2 ^ (prefixWord ++ tailWord_6244935).sum := by decide
  have hdescent : baseEnd_6244935 < baseStart_6244935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244944 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_6244944 : Nat := 118140960795 + 6244944 * 2 ^ 59
def prefixEnd_6244944 : Nat := 4983230072969 + 3 ^ 40 * 6244944 * 2
def baseEnd_6244944 : Nat := 1068885977470506620526677

theorem tailTrace_6244944 : CollatzResearch.WordTrace tailWord_6244944 prefixEnd_6244944 1068885977470506620526677 := by
  unfold tailWord_6244944
  simp only [CollatzResearch.WordTrace]
  refine ⟨113885909943820957183902943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151847879925094609578537257 113885909943820957183902943)
  ·
    refine ⟨170828864915731435775854415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113885909943820957183902943 170828864915731435775854415)
    ·
      refine ⟨256243297373597153663781623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170828864915731435775854415 256243297373597153663781623)
      ·
        refine ⟨384364946060395730495672435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256243297373597153663781623 384364946060395730495672435)
        ·
          refine ⟨576547419090593595743508653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384364946060395730495672435 576547419090593595743508653)
          ·
            refine ⟨216205282158972598403815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576547419090593595743508653 216205282158972598403815745)
            ·
              refine ⟨162153961619229448802861809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216205282158972598403815745 162153961619229448802861809)
              ·
                refine ⟨121615471214422086602146357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162153961619229448802861809 121615471214422086602146357)
                ·
                  refine ⟨11401450426352070618951221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121615471214422086602146357 11401450426352070618951221)
                  ·
                    refine ⟨1068885977470506620526677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11401450426352070618951221 1068885977470506620526677)
                    ·
                      rfl

theorem cell23_6244944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_6244944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244944 prefixEnd_6244944 := by exact prefixLift 6244944
  have htrace : WordTrace (prefixWord ++ tailWord_6244944) baseStart_6244944 baseEnd_6244944 := by
    simpa [prefixWord, tailWord_6244944, baseEnd_6244944] using wordTrace_append hprefix tailTrace_6244944
  have hstable : (prefixWord ++ tailWord_6244944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244944).length < 2 ^ (prefixWord ++ tailWord_6244944).sum := by decide
  have hdescent : baseEnd_6244944 < baseStart_6244944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244948 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 6]
def baseStart_6244948 : Nat := 118140960795 + 6244948 * 2 ^ 59
def prefixEnd_6244948 : Nat := 4983230072969 + 3 ^ 40 * 6244948 * 2
def baseEnd_6244948 : Nat := 356295554037126427325557

theorem tailTrace_6244948 : CollatzResearch.WordTrace tailWord_6244948 prefixEnd_6244948 356295554037126427325557 := by
  unfold tailWord_6244948
  simp only [CollatzResearch.WordTrace]
  refine ⟨113885982889813711525475749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151847977186418282033967665 113885982889813711525475749)
  ·
    refine ⟨21353621791840070911026703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113885982889813711525475749 21353621791840070911026703)
    ·
      refine ⟨32030432687760106366540055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21353621791840070911026703 32030432687760106366540055)
      ·
        refine ⟨48045649031640159549810083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32030432687760106366540055 48045649031640159549810083)
        ·
          refine ⟨72068473547460239324715125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48045649031640159549810083 72068473547460239324715125)
          ·
            refine ⟨6756419395074397436692043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72068473547460239324715125 6756419395074397436692043)
            ·
              refine ⟨10134629092611596155038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756419395074397436692043 10134629092611596155038065)
              ·
                refine ⟨7600971819458697116278549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10134629092611596155038065 7600971819458697116278549)
                ·
                  refine ⟨356295554037126427325557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7600971819458697116278549 356295554037126427325557)
                  ·
                    rfl

theorem cell23_6244948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_6244948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244948 prefixEnd_6244948 := by exact prefixLift 6244948
  have htrace : WordTrace (prefixWord ++ tailWord_6244948) baseStart_6244948 baseEnd_6244948 := by
    simpa [prefixWord, tailWord_6244948, baseEnd_6244948] using wordTrace_append hprefix tailTrace_6244948
  have hstable : (prefixWord ++ tailWord_6244948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244948).length < 2 ^ (prefixWord ++ tailWord_6244948).sum := by decide
  have hdescent : baseEnd_6244948 < baseStart_6244948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6244992 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 1, 1, 3]
def baseStart_6244992 : Nat := 118140960795 + 6244992 * 2 ^ 59
def prefixEnd_6244992 : Nat := 4983230072969 + 3 ^ 40 * 6244992 * 2
def baseEnd_6244992 : Nat := 3206682579482935673779811

theorem tailTrace_6244992 : CollatzResearch.WordTrace tailWord_6244992 prefixEnd_6244992 3206682579482935673779811 := by
  unfold tailWord_6244992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113886785295734009282776615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151849047060978679043702153 113886785295734009282776615)
  ·
    refine ⟨170830177943601013924164923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113886785295734009282776615 170830177943601013924164923)
    ·
      refine ⟨256245266915401520886247385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170830177943601013924164923 256245266915401520886247385)
      ·
        refine ⟨192183950186551140664685539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256245266915401520886247385 192183950186551140664685539)
        ·
          refine ⟨288275925279826710997028309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192183950186551140664685539 288275925279826710997028309)
          ·
            refine ⟨6756466998745938538992851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 288275925279826710997028309 6756466998745938538992851)
            ·
              refine ⟨10134700498118907808489277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756466998745938538992851 10134700498118907808489277)
              ·
                refine ⟨3800512686794590428183479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10134700498118907808489277 3800512686794590428183479)
                ·
                  refine ⟨5700769030191885642275219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800512686794590428183479 5700769030191885642275219)
                  ·
                    refine ⟨8551153545287828463412829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5700769030191885642275219 8551153545287828463412829)
                    ·
                      refine ⟨3206682579482935673779811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551153545287828463412829 3206682579482935673779811)
                      ·
                        rfl

theorem cell23_6244992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_6244992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6244992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6244992 prefixEnd_6244992 := by exact prefixLift 6244992
  have htrace : WordTrace (prefixWord ++ tailWord_6244992) baseStart_6244992 baseEnd_6244992 := by
    simpa [prefixWord, tailWord_6244992, baseEnd_6244992] using wordTrace_append hprefix tailTrace_6244992
  have hstable : (prefixWord ++ tailWord_6244992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6244992).length < 2 ^ (prefixWord ++ tailWord_6244992).sum := by decide
  have hdescent : baseEnd_6244992 < baseStart_6244992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6244992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245001 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_6245001 : Nat := 118140960795 + 6245001 * 2 ^ 59
def prefixEnd_6245001 : Nat := 4983230072969 + 3 ^ 40 * 6245001 * 2
def baseEnd_6245001 : Nat := 3206687200808826138567269

theorem tailTrace_6245001 : CollatzResearch.WordTrace tailWord_6245001 prefixEnd_6245001 3206687200808826138567269 := by
  unfold tailWord_6245001
  simp only [CollatzResearch.WordTrace]
  refine ⟨227773898848435413102630857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151849265898956942068420571 227773898848435413102630857)
  ·
    refine ⟨170830424136326559826973143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227773898848435413102630857 170830424136326559826973143)
    ·
      refine ⟨256245636204489839740459715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170830424136326559826973143 256245636204489839740459715)
      ·
        refine ⟨384368454306734759610689573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256245636204489839740459715 384368454306734759610689573)
        ·
          refine ⟨72069085182512767427004295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384368454306734759610689573 72069085182512767427004295)
          ·
            refine ⟨108103627773769151140506443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72069085182512767427004295 108103627773769151140506443)
            ·
              refine ⟨162155441660653726710759665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108103627773769151140506443 162155441660653726710759665)
              ·
                refine ⟨121616581245490295033069749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162155441660653726710759665 121616581245490295033069749)
                ·
                  refine ⟨11401554491764715159350289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121616581245490295033069749 11401554491764715159350289)
                  ·
                    refine ⟨8551165868823536369512717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11401554491764715159350289 8551165868823536369512717)
                    ·
                      refine ⟨3206687200808826138567269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551165868823536369512717 3206687200808826138567269)
                      ·
                        rfl

theorem cell23_6245001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_6245001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245001 prefixEnd_6245001 := by exact prefixLift 6245001
  have htrace : WordTrace (prefixWord ++ tailWord_6245001) baseStart_6245001 baseEnd_6245001 := by
    simpa [prefixWord, tailWord_6245001, baseEnd_6245001] using wordTrace_append hprefix tailTrace_6245001
  have hstable : (prefixWord ++ tailWord_6245001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245001).length < 2 ^ (prefixWord ++ tailWord_6245001).sum := by decide
  have hdescent : baseEnd_6245001 < baseStart_6245001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245025 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6245025 : Nat := 118140960795 + 6245025 * 2 ^ 59
def prefixEnd_6245025 : Nat := 4983230072969 + 3 ^ 40 * 6245025 * 2
def baseEnd_6245025 : Nat := 1068899841448178014889053

theorem tailTrace_6245025 : CollatzResearch.WordTrace tailWord_6245025 prefixEnd_6245025 1068899841448178014889053 := by
  unfold tailWord_6245025
  simp only [CollatzResearch.WordTrace]
  refine ⟨227774774200348465201504529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151849849466898976801003019 227774774200348465201504529)
  ·
    refine ⟨170831080650261348901128397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227774774200348465201504529 170831080650261348901128397)
    ·
      refine ⟨64061655243848005837923149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170831080650261348901128397 64061655243848005837923149)
      ·
        refine ⟨24023120716443002189221181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64061655243848005837923149 24023120716443002189221181)
        ·
          refine ⟨9008670268666125820957943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24023120716443002189221181 9008670268666125820957943)
          ·
            refine ⟨13513005402999188731436915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008670268666125820957943 13513005402999188731436915)
            ·
              refine ⟨20269508104498783097155373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13513005402999188731436915 20269508104498783097155373)
              ·
                refine ⟨7601065539187043661433265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20269508104498783097155373 7601065539187043661433265)
                ·
                  refine ⟨5700799154390282746074949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601065539187043661433265 5700799154390282746074949)
                  ·
                    refine ⟨1068899841448178014889053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700799154390282746074949 1068899841448178014889053)
                    ·
                      rfl

theorem cell23_6245025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6245025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245025 prefixEnd_6245025 := by exact prefixLift 6245025
  have htrace : WordTrace (prefixWord ++ tailWord_6245025) baseStart_6245025 baseEnd_6245025 := by
    simpa [prefixWord, tailWord_6245025, baseEnd_6245025] using wordTrace_append hprefix tailTrace_6245025
  have hstable : (prefixWord ++ tailWord_6245025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245025).length < 2 ^ (prefixWord ++ tailWord_6245025).sum := by decide
  have hdescent : baseEnd_6245025 < baseStart_6245025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245038 : List Nat := [4, 1, 4, 1, 1, 1, 2, 9]
def baseStart_6245038 : Nat := 118140960795 + 6245038 * 2 ^ 59
def prefixEnd_6245038 : Nat := 4983230072969 + 3 ^ 40 * 6245038 * 2
def baseEnd_6245038 : Nat := 118766896281223796066837

theorem tailTrace_6245038 : CollatzResearch.WordTrace tailWord_6245038 prefixEnd_6245038 118766896281223796066837 := by
  unfold tailWord_6245038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471906043662671052715971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151850165566200912281151845 28471906043662671052715971)
  ·
    refine ⟨42707859065494006579073957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28471906043662671052715971 42707859065494006579073957)
    ·
      refine ⟨8007723574780126233576367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42707859065494006579073957 8007723574780126233576367)
      ·
        refine ⟨12011585362170189350364551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007723574780126233576367 12011585362170189350364551)
        ·
          refine ⟨18017378043255284025546827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011585362170189350364551 18017378043255284025546827)
          ·
            refine ⟨27026067064882926038320241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18017378043255284025546827 27026067064882926038320241)
            ·
              refine ⟨20269550298662194528740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27026067064882926038320241 20269550298662194528740181)
              ·
                refine ⟨118766896281223796066837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20269550298662194528740181 118766896281223796066837)
                ·
                  rfl

theorem cell23_6245038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_6245038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245038 prefixEnd_6245038 := by exact prefixLift 6245038
  have htrace : WordTrace (prefixWord ++ tailWord_6245038) baseStart_6245038 baseEnd_6245038 := by
    simpa [prefixWord, tailWord_6245038, baseEnd_6245038] using wordTrace_append hprefix tailTrace_6245038
  have hstable : (prefixWord ++ tailWord_6245038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245038).length < 2 ^ (prefixWord ++ tailWord_6245038).sum := by decide
  have hdescent : baseEnd_6245038 < baseStart_6245038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245066 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_6245066 : Nat := 118140960795 + 6245066 * 2 ^ 59
def prefixEnd_6245066 : Nat := 4983230072969 + 3 ^ 40 * 6245066 * 2
def baseEnd_6245066 : Nat := 3206720577051368384254471

theorem tailTrace_6245066 : CollatzResearch.WordTrace tailWord_6245066 prefixEnd_6245066 3206720577051368384254471 := by
  unfold tailWord_6245066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56944067398299982300936763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151850846395466619469164701 56944067398299982300936763)
  ·
    refine ⟨85416101097449973451405145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56944067398299982300936763 85416101097449973451405145)
    ·
      refine ⟨64062075823087480088553859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85416101097449973451405145 64062075823087480088553859)
      ·
        refine ⟨96093113734631220132830789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64062075823087480088553859 96093113734631220132830789)
        ·
          refine ⟨18017458825243353774905773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96093113734631220132830789 18017458825243353774905773)
          ·
            refine ⟨6756547059466257665589665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18017458825243353774905773 6756547059466257665589665)
            ·
              refine ⟨5067410294599693249192249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756547059466257665589665 5067410294599693249192249)
              ·
                refine ⟨3800557720949769936894187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5067410294599693249192249 3800557720949769936894187)
                ·
                  refine ⟨5700836581424654905341281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800557720949769936894187 5700836581424654905341281)
                  ·
                    refine ⟨4275627436068491179005961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700836581424654905341281 4275627436068491179005961)
                    ·
                      refine ⟨3206720577051368384254471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275627436068491179005961 3206720577051368384254471)
                      ·
                        rfl

theorem cell23_6245066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_6245066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245066 prefixEnd_6245066 := by exact prefixLift 6245066
  have htrace : WordTrace (prefixWord ++ tailWord_6245066) baseStart_6245066 baseEnd_6245066 := by
    simpa [prefixWord, tailWord_6245066, baseEnd_6245066] using wordTrace_append hprefix tailTrace_6245066
  have hstable : (prefixWord ++ tailWord_6245066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245066).length < 2 ^ (prefixWord ++ tailWord_6245066).sum := by decide
  have hdescent : baseEnd_6245066 < baseStart_6245066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245081 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_6245081 : Nat := 118140960795 + 6245081 * 2 ^ 59
def prefixEnd_6245081 : Nat := 4983230072969 + 3 ^ 40 * 6245081 * 2
def baseEnd_6245081 : Nat := 1068909426420395275188967

theorem tailTrace_6245081 : CollatzResearch.WordTrace tailWord_6245081 prefixEnd_6245081 1068909426420395275188967 := by
  unfold tailWord_6245081
  simp only [CollatzResearch.WordTrace]
  refine ⟨227776816688145586765543097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151851211125430391177028731 227776816688145586765543097)
  ·
    refine ⟨170832612516109190074157323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227776816688145586765543097 170832612516109190074157323)
    ·
      refine ⟨256248918774163785111235985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170832612516109190074157323 256248918774163785111235985)
      ·
        refine ⟨192186689080622838833426989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256248918774163785111235985 192186689080622838833426989)
        ·
          refine ⟨72070008405233564562535121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192186689080622838833426989 72070008405233564562535121)
          ·
            refine ⟨54052506303925173421901341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72070008405233564562535121 54052506303925173421901341)
            ·
              refine ⟨20269689863971940033213003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54052506303925173421901341 20269689863971940033213003)
              ·
                refine ⟨30404534795957910049819505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20269689863971940033213003 30404534795957910049819505)
                ·
                  refine ⟨22803401096968432537364629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30404534795957910049819505 22803401096968432537364629)
                  ·
                    refine ⟨1068909426420395275188967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22803401096968432537364629 1068909426420395275188967)
                    ·
                      rfl

theorem cell23_6245081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_6245081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245081 prefixEnd_6245081 := by exact prefixLift 6245081
  have htrace : WordTrace (prefixWord ++ tailWord_6245081) baseStart_6245081 baseEnd_6245081 := by
    simpa [prefixWord, tailWord_6245081, baseEnd_6245081] using wordTrace_append hprefix tailTrace_6245081
  have hstable : (prefixWord ++ tailWord_6245081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245081).length < 2 ^ (prefixWord ++ tailWord_6245081).sum := by decide
  have hdescent : baseEnd_6245081 < baseStart_6245081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245105 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_6245105 : Nat := 118140960795 + 6245105 * 2 ^ 59
def prefixEnd_6245105 : Nat := 4983230072969 + 3 ^ 40 * 6245105 * 2
def baseEnd_6245105 : Nat := 3206740602796893731666791

theorem tailTrace_6245105 : CollatzResearch.WordTrace tailWord_6245105 prefixEnd_6245105 3206740602796893731666791 := by
  unfold tailWord_6245105
  simp only [CollatzResearch.WordTrace]
  refine ⟨227777692040058638864416769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151851794693372425909611179 227777692040058638864416769)
  ·
    refine ⟨170833269030043979148312577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227777692040058638864416769 170833269030043979148312577)
    ·
      refine ⟨128124951772532984361234433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170833269030043979148312577 128124951772532984361234433)
      ·
        refine ⟨96093713829399738270925825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128124951772532984361234433 96093713829399738270925825)
        ·
          refine ⟨72070285372049803703194369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96093713829399738270925825 72070285372049803703194369)
          ·
            refine ⟨54052714029037352777395777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72070285372049803703194369 54052714029037352777395777)
            ·
              refine ⟨40539535521778014583046833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54052714029037352777395777 40539535521778014583046833)
              ·
                refine ⟨30404651641333510937285125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40539535521778014583046833 30404651641333510937285125)
                ·
                  refine ⟨5700872182750033300740961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30404651641333510937285125 5700872182750033300740961)
                  ·
                    refine ⟨4275654137062524975555721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700872182750033300740961 4275654137062524975555721)
                    ·
                      refine ⟨3206740602796893731666791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275654137062524975555721 3206740602796893731666791)
                      ·
                        rfl

theorem cell23_6245105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_6245105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245105 prefixEnd_6245105 := by exact prefixLift 6245105
  have htrace : WordTrace (prefixWord ++ tailWord_6245105) baseStart_6245105 baseEnd_6245105 := by
    simpa [prefixWord, tailWord_6245105, baseEnd_6245105] using wordTrace_append hprefix tailTrace_6245105
  have hstable : (prefixWord ++ tailWord_6245105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245105).length < 2 ^ (prefixWord ++ tailWord_6245105).sum := by decide
  have hdescent : baseEnd_6245105 < baseStart_6245105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245128 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 7]
def baseStart_6245128 : Nat := 118140960795 + 6245128 * 2 ^ 59
def prefixEnd_6245128 : Nat := 4983230072969 + 3 ^ 40 * 6245128 * 2
def baseEnd_6245128 : Nat := 356305823650216349075465

theorem tailTrace_6245128 : CollatzResearch.WordTrace tailWord_6245128 prefixEnd_6245128 356305823650216349075465 := by
  unfold tailWord_6245128
  simp only [CollatzResearch.WordTrace]
  refine ⟨113889265459487656896252019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151852353945983542528336025 113889265459487656896252019)
  ·
    refine ⟨170833898189231485344378029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113889265459487656896252019 170833898189231485344378029)
    ·
      refine ⟨64062711820961807004141761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170833898189231485344378029 64062711820961807004141761)
      ·
        refine ⟨48047033865721355253106321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64062711820961807004141761 48047033865721355253106321)
        ·
          refine ⟨36035275399291016439829741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48047033865721355253106321 36035275399291016439829741)
          ·
            refine ⟨13513228274734131164936153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36035275399291016439829741 13513228274734131164936153)
            ·
              refine ⟨10134921206050598373702115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13513228274734131164936153 10134921206050598373702115)
              ·
                refine ⟨15202381809075897560553173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134921206050598373702115 15202381809075897560553173)
                ·
                  refine ⟨356305823650216349075465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15202381809075897560553173 356305823650216349075465)
                  ·
                    rfl

theorem cell23_6245128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_6245128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245128 prefixEnd_6245128 := by exact prefixLift 6245128
  have htrace : WordTrace (prefixWord ++ tailWord_6245128) baseStart_6245128 baseEnd_6245128 := by
    simpa [prefixWord, tailWord_6245128, baseEnd_6245128] using wordTrace_append hprefix tailTrace_6245128
  have hstable : (prefixWord ++ tailWord_6245128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245128).length < 2 ^ (prefixWord ++ tailWord_6245128).sum := by decide
  have hdescent : baseEnd_6245128 < baseStart_6245128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245141 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_6245141 : Nat := 118140960795 + 6245141 * 2 ^ 59
def prefixEnd_6245141 : Nat := 4983230072969 + 3 ^ 40 * 6245141 * 2
def baseEnd_6245141 : Nat := 1068919696033485196938875

theorem tailTrace_6245141 : CollatzResearch.WordTrace tailWord_6245141 prefixEnd_6245141 1068919696033485196938875 := by
  unfold tailWord_6245141
  simp only [CollatzResearch.WordTrace]
  refine ⟨227779005067928217012727277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151852670045285478008484851 227779005067928217012727277)
  ·
    refine ⟨85417126900473081379772729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227779005067928217012727277 85417126900473081379772729)
    ·
      refine ⟨64062845175354811034829547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85417126900473081379772729 64062845175354811034829547)
      ·
        refine ⟨96094267763032216552244321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64062845175354811034829547 96094267763032216552244321)
        ·
          refine ⟨72070700822274162414183241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96094267763032216552244321 72070700822274162414183241)
          ·
            refine ⟨54053025616705621810637431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72070700822274162414183241 54053025616705621810637431)
            ·
              refine ⟨81079538425058432715956147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54053025616705621810637431 81079538425058432715956147)
              ·
                refine ⟨121619307637587649073934221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81079538425058432715956147 121619307637587649073934221)
                ·
                  refine ⟨45607240364095368402725333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121619307637587649073934221 45607240364095368402725333)
                  ·
                    refine ⟨1068919696033485196938875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45607240364095368402725333 1068919696033485196938875)
                    ·
                      rfl

theorem cell23_6245141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_6245141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245141 prefixEnd_6245141 := by exact prefixLift 6245141
  have htrace : WordTrace (prefixWord ++ tailWord_6245141) baseStart_6245141 baseEnd_6245141 := by
    simpa [prefixWord, tailWord_6245141, baseEnd_6245141] using wordTrace_append hprefix tailTrace_6245141
  have hstable : (prefixWord ++ tailWord_6245141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245141).length < 2 ^ (prefixWord ++ tailWord_6245141).sum := by decide
  have hdescent : baseEnd_6245141 < baseStart_6245141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245190 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6245190 : Nat := 118140960795 + 6245190 * 2 ^ 59
def prefixEnd_6245190 : Nat := 4983230072969 + 3 ^ 40 * 6245190 * 2
def baseEnd_6245190 : Nat := 3206784248652525899103901

theorem tailTrace_6245190 : CollatzResearch.WordTrace tailWord_6245190 prefixEnd_6245190 3206784248652525899103901 := by
  unfold tailWord_6245190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118149757648459324414407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151853861496500465587507349 7118149757648459324414407)
  ·
    refine ⟨10677224636472688986621611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7118149757648459324414407 10677224636472688986621611)
    ·
      refine ⟨16015836954709033479932417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10677224636472688986621611 16015836954709033479932417)
      ·
        refine ⟨12011877716031775109949313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015836954709033479932417 12011877716031775109949313)
        ·
          refine ⟨9008908287023831332461985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12011877716031775109949313 9008908287023831332461985)
          ·
            refine ⟨6756681215267873499346489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9008908287023831332461985 6756681215267873499346489)
            ·
              refine ⟨5067510911450905124509867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756681215267873499346489 5067510911450905124509867)
              ·
                refine ⟨7601266367176357686764801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067510911450905124509867 7601266367176357686764801)
                ·
                  refine ⟨5700949775382268265073601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601266367176357686764801 5700949775382268265073601)
                  ·
                    refine ⟨4275712331536701198805201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5700949775382268265073601 4275712331536701198805201)
                    ·
                      refine ⟨3206784248652525899103901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275712331536701198805201 3206784248652525899103901)
                      ·
                        rfl

theorem cell23_6245190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6245190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245190 prefixEnd_6245190 := by exact prefixLift 6245190
  have htrace : WordTrace (prefixWord ++ tailWord_6245190) baseStart_6245190 baseEnd_6245190 := by
    simpa [prefixWord, tailWord_6245190, baseEnd_6245190] using wordTrace_append hprefix tailTrace_6245190
  have hstable : (prefixWord ++ tailWord_6245190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245190).length < 2 ^ (prefixWord ++ tailWord_6245190).sum := by decide
  have hdescent : baseEnd_6245190 < baseStart_6245190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245198 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_6245198 : Nat := 118140960795 + 6245198 * 2 ^ 59
def prefixEnd_6245198 : Nat := 4983230072969 + 3 ^ 40 * 6245198 * 2
def baseEnd_6245198 : Nat := 3206788356497761867803863

theorem tailTrace_6245198 : CollatzResearch.WordTrace tailWord_6245198 prefixEnd_6245198 3206788356497761867803863 := by
  unfold tailWord_6245198
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472635503590214468444031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151854056019147810498368165 28472635503590214468444031)
  ·
    refine ⟨42708953255385321702666047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28472635503590214468444031 42708953255385321702666047)
    ·
      refine ⟨64063429883077982553999071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42708953255385321702666047 64063429883077982553999071)
      ·
        refine ⟨96095144824616973830998607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64063429883077982553999071 96095144824616973830998607)
        ·
          refine ⟨144142717236925460746497911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96095144824616973830998607 144142717236925460746497911)
          ·
            refine ⟨216214075855388191119746867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144142717236925460746497911 216214075855388191119746867)
            ·
              refine ⟨324321113783082286679620301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216214075855388191119746867 324321113783082286679620301)
              ·
                refine ⟨121620417668655857504857613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324321113783082286679620301 121620417668655857504857613)
                ·
                  refine ⟨45607656625745946564321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121620417668655857504857613 45607656625745946564321605)
                  ·
                    refine ⟨8551435617327364980810301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45607656625745946564321605 8551435617327364980810301)
                    ·
                      refine ⟨3206788356497761867803863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551435617327364980810301 3206788356497761867803863)
                      ·
                        rfl

theorem cell23_6245198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_6245198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245198 prefixEnd_6245198 := by exact prefixLift 6245198
  have htrace : WordTrace (prefixWord ++ tailWord_6245198) baseStart_6245198 baseEnd_6245198 := by
    simpa [prefixWord, tailWord_6245198, baseEnd_6245198] using wordTrace_append hprefix tailTrace_6245198
  have hstable : (prefixWord ++ tailWord_6245198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245198).length < 2 ^ (prefixWord ++ tailWord_6245198).sum := by decide
  have hdescent : baseEnd_6245198 < baseStart_6245198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245212 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6245212 : Nat := 118140960795 + 6245212 * 2 ^ 59
def prefixEnd_6245212 : Nat := 4983230072969 + 3 ^ 40 * 6245212 * 2
def baseEnd_6245212 : Nat := 3206795545226924813028799

theorem tailTrace_6245212 : CollatzResearch.WordTrace tailWord_6245212 prefixEnd_6245212 3206795545226924813028799 := by
  unfold tailWord_6245212
  simp only [CollatzResearch.WordTrace]
  refine ⟨113890797325335498069280945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151854396433780664092374593 113890797325335498069280945)
  ·
    refine ⟨85418097994001623551960709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113890797325335498069280945 85418097994001623551960709)
    ·
      refine ⟨16015893373875304415992633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85418097994001623551960709 16015893373875304415992633)
      ·
        refine ⟨12011920030406478311994475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015893373875304415992633 12011920030406478311994475)
        ·
          refine ⟨18017880045609717467991713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011920030406478311994475 18017880045609717467991713)
          ·
            refine ⟨13513410034207288100993785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18017880045609717467991713 13513410034207288100993785)
            ·
              refine ⟨10135057525655466075745339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13513410034207288100993785 10135057525655466075745339)
              ·
                refine ⟨15202586288483199113618009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135057525655466075745339 15202586288483199113618009)
                ·
                  refine ⟨11401939716362399335213507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15202586288483199113618009 11401939716362399335213507)
                  ·
                    refine ⟨17102909574543599002820261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11401939716362399335213507 17102909574543599002820261)
                    ·
                      refine ⟨3206795545226924813028799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17102909574543599002820261 3206795545226924813028799)
                      ·
                        rfl

theorem cell23_6245212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6245212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245212 prefixEnd_6245212 := by exact prefixLift 6245212
  have htrace : WordTrace (prefixWord ++ tailWord_6245212) baseStart_6245212 baseEnd_6245212 := by
    simpa [prefixWord, tailWord_6245212, baseEnd_6245212] using wordTrace_append hprefix tailTrace_6245212
  have hstable : (prefixWord ++ tailWord_6245212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245212).length < 2 ^ (prefixWord ++ tailWord_6245212).sum := by decide
  have hdescent : baseEnd_6245212 < baseStart_6245212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245215 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_6245215 : Nat := 118140960795 + 6245215 * 2 ^ 59
def prefixEnd_6245215 : Nat := 4983230072969 + 3 ^ 40 * 6245215 * 2
def baseEnd_6245215 : Nat := 3206797085668888301291285

theorem tailTrace_6245215 : CollatzResearch.WordTrace tailWord_6245215 prefixEnd_6245215 3206797085668888301291285 := by
  unfold tailWord_6245215
  simp only [CollatzResearch.WordTrace]
  refine ⟨227781704069660127650921099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151854469379773418433947399 227781704069660127650921099)
  ·
    refine ⟨341672556104490191476381649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227781704069660127650921099 341672556104490191476381649)
    ·
      refine ⟨256254417078367643607286237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341672556104490191476381649 256254417078367643607286237)
      ·
        refine ⟨96095406404387866352732339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256254417078367643607286237 96095406404387866352732339)
        ·
          refine ⟨144143109606581799529098509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96095406404387866352732339 144143109606581799529098509)
          ·
            refine ⟨54053666102468174823411941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144143109606581799529098509 54053666102468174823411941)
            ·
              refine ⟨10135062394212782779389739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54053666102468174823411941 10135062394212782779389739)
              ·
                refine ⟨15202593591319174169084609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135062394212782779389739 15202593591319174169084609)
                ·
                  refine ⟨11401945193489380626813457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15202593591319174169084609 11401945193489380626813457)
                  ·
                    refine ⟨8551458895117035470110093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11401945193489380626813457 8551458895117035470110093)
                    ·
                      refine ⟨3206797085668888301291285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551458895117035470110093 3206797085668888301291285)
                      ·
                        rfl

theorem cell23_6245215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_6245215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245215 prefixEnd_6245215 := by exact prefixLift 6245215
  have htrace : WordTrace (prefixWord ++ tailWord_6245215) baseStart_6245215 baseEnd_6245215 := by
    simpa [prefixWord, tailWord_6245215, baseEnd_6245215] using wordTrace_append hprefix tailTrace_6245215
  have hstable : (prefixWord ++ tailWord_6245215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245215).length < 2 ^ (prefixWord ++ tailWord_6245215).sum := by decide
  have hdescent : baseEnd_6245215 < baseStart_6245215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245266 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6245266 : Nat := 118140960795 + 6245266 * 2 ^ 59
def prefixEnd_6245266 : Nat := 4983230072969 + 3 ^ 40 * 6245266 * 2
def baseEnd_6245266 : Nat := 3206823273182267601753551

theorem tailTrace_6245266 : CollatzResearch.WordTrace tailWord_6245266 prefixEnd_6245266 3206823273182267601753551 := by
  unfold tailWord_6245266
  simp only [CollatzResearch.WordTrace]
  refine ⟨56945891048118840840256913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151855709461650242240685101 56945891048118840840256913)
  ·
    refine ⟨42709418286089130630192685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56945891048118840840256913 42709418286089130630192685)
    ·
      refine ⟨16016031857283423986322257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42709418286089130630192685 16016031857283423986322257)
      ·
        refine ⟨12012023892962567989741693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16016031857283423986322257 12012023892962567989741693)
        ·
          refine ⟨4504508959860962996153135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12012023892962567989741693 4504508959860962996153135)
          ·
            refine ⟨6756763439791444494229703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504508959860962996153135 6756763439791444494229703)
            ·
              refine ⟨10135145159687166741344555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756763439791444494229703 10135145159687166741344555)
              ·
                refine ⟨15202717739530750112016833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135145159687166741344555 15202717739530750112016833)
                ·
                  refine ⟨11402038304648062584012625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15202717739530750112016833 11402038304648062584012625)
                  ·
                    refine ⟨8551528728486046938009469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11402038304648062584012625 8551528728486046938009469)
                    ·
                      refine ⟨3206823273182267601753551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551528728486046938009469 3206823273182267601753551)
                      ·
                        rfl

theorem cell23_6245266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6245266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245266 prefixEnd_6245266 := by exact prefixLift 6245266
  have htrace : WordTrace (prefixWord ++ tailWord_6245266) baseStart_6245266 baseEnd_6245266 := by
    simpa [prefixWord, tailWord_6245266, baseEnd_6245266] using wordTrace_append hprefix tailTrace_6245266
  have hstable : (prefixWord ++ tailWord_6245266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245266).length < 2 ^ (prefixWord ++ tailWord_6245266).sum := by decide
  have hdescent : baseEnd_6245266 < baseStart_6245266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245279 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6245279 : Nat := 118140960795 + 6245279 * 2 ^ 59
def prefixEnd_6245279 : Nat := 4983230072969 + 3 ^ 40 * 6245279 * 2
def baseEnd_6245279 : Nat := 3206829948430776050890991

theorem tailTrace_6245279 : CollatzResearch.WordTrace tailWord_6245279 prefixEnd_6245279 3206829948430776050890991 := by
  unfold tailWord_6245279
  simp only [CollatzResearch.WordTrace]
  refine ⟨227784038341428266581250891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151856025560952177720833927 227784038341428266581250891)
  ·
    refine ⟨341676057512142399871876337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227784038341428266581250891 341676057512142399871876337)
    ·
      refine ⟨256257043134106799903907253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341676057512142399871876337 256257043134106799903907253)
      ·
        refine ⟨24024097793822512490991305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256257043134106799903907253 24024097793822512490991305)
        ·
          refine ⟨18018073345366884368243479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24024097793822512490991305 18018073345366884368243479)
          ·
            refine ⟨27027110018050326552365219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018073345366884368243479 27027110018050326552365219)
            ·
              refine ⟨40540665027075489828547829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27027110018050326552365219 40540665027075489828547829)
              ·
                refine ⟨3800687346288327171426359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40540665027075489828547829 3800687346288327171426359)
                ·
                  refine ⟨5701031019432490757139539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800687346288327171426359 5701031019432490757139539)
                  ·
                    refine ⟨8551546529148736135709309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5701031019432490757139539 8551546529148736135709309)
                    ·
                      refine ⟨3206829948430776050890991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551546529148736135709309 3206829948430776050890991)
                      ·
                        rfl

theorem cell23_6245279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6245279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245279 prefixEnd_6245279 := by exact prefixLift 6245279
  have htrace : WordTrace (prefixWord ++ tailWord_6245279) baseStart_6245279 baseEnd_6245279 := by
    simpa [prefixWord, tailWord_6245279, baseEnd_6245279] using wordTrace_append hprefix tailTrace_6245279
  have hstable : (prefixWord ++ tailWord_6245279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245279).length < 2 ^ (prefixWord ++ tailWord_6245279).sum := by decide
  have hdescent : baseEnd_6245279 < baseStart_6245279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245282 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6245282 : Nat := 118140960795 + 6245282 * 2 ^ 59
def prefixEnd_6245282 : Nat := 4983230072969 + 3 ^ 40 * 6245282 * 2
def baseEnd_6245282 : Nat := 1068943829624246513051159

theorem tailTrace_6245282 : CollatzResearch.WordTrace tailWord_6245282 prefixEnd_6245282 1068943829624246513051159 := by
  unfold tailWord_6245282
  simp only [CollatzResearch.WordTrace]
  refine ⟨56946036940104349523402525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151856098506944932062406733 56946036940104349523402525)
  ·
    refine ⟨21354763852539131071275947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56946036940104349523402525 21354763852539131071275947)
    ·
      refine ⟨32032145778808696606913921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21354763852539131071275947 32032145778808696606913921)
      ·
        refine ⟨24024109334106522455185441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32032145778808696606913921 24024109334106522455185441)
        ·
          refine ⟨18018082000579891841389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24024109334106522455185441 18018082000579891841389081)
          ·
            refine ⟨13513561500434918881041811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18018082000579891841389081 13513561500434918881041811)
            ·
              refine ⟨20270342250652378321562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13513561500434918881041811 20270342250652378321562717)
              ·
                refine ⟨7601378343994641870586019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20270342250652378321562717 7601378343994641870586019)
                ·
                  refine ⟨11402067515991962805879029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7601378343994641870586019 11402067515991962805879029)
                  ·
                    refine ⟨1068943829624246513051159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11402067515991962805879029 1068943829624246513051159)
                    ·
                      rfl

theorem cell23_6245282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6245282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245282 prefixEnd_6245282 := by exact prefixLift 6245282
  have htrace : WordTrace (prefixWord ++ tailWord_6245282) baseStart_6245282 baseEnd_6245282 := by
    simpa [prefixWord, tailWord_6245282, baseEnd_6245282] using wordTrace_append hprefix tailTrace_6245282
  have hstable : (prefixWord ++ tailWord_6245282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245282).length < 2 ^ (prefixWord ++ tailWord_6245282).sum := by decide
  have hdescent : baseEnd_6245282 < baseStart_6245282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245295 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 2, 4]
def baseStart_6245295 : Nat := 118140960795 + 6245295 * 2 ^ 59
def prefixEnd_6245295 : Nat := 4983230072969 + 3 ^ 40 * 6245295 * 2
def baseEnd_6245295 : Nat := 1068946054707082662763639

theorem tailTrace_6245295 : CollatzResearch.WordTrace tailWord_6245295 prefixEnd_6245295 1068946054707082662763639 := by
  unfold tailWord_6245295
  simp only [CollatzResearch.WordTrace]
  refine ⟨227784621909370301313833339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151856414606246867542555559 227784621909370301313833339)
  ·
    refine ⟨341676932864055451970750009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227784621909370301313833339 341676932864055451970750009)
    ·
      refine ⟨256257699648041588978062507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341676932864055451970750009 256257699648041588978062507)
      ·
        refine ⟨384386549472062383467093761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256257699648041588978062507 384386549472062383467093761)
        ·
          refine ⟨288289912104046787600320321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384386549472062383467093761 288289912104046787600320321)
          ·
            refine ⟨216217434078035090700240241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288289912104046787600320321 216217434078035090700240241)
            ·
              refine ⟨162163075558526318025180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216217434078035090700240241 162163075558526318025180181)
              ·
                refine ⟨7601394166805921157430321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162163075558526318025180181 7601394166805921157430321)
                ·
                  refine ⟨5701045625104440868072741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601394166805921157430321 5701045625104440868072741)
                  ·
                    refine ⟨1068946054707082662763639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701045625104440868072741 1068946054707082662763639)
                    ·
                      rfl

theorem cell23_6245295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_6245295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245295 prefixEnd_6245295 := by exact prefixLift 6245295
  have htrace : WordTrace (prefixWord ++ tailWord_6245295) baseStart_6245295 baseEnd_6245295 := by
    simpa [prefixWord, tailWord_6245295, baseEnd_6245295] using wordTrace_append hprefix tailTrace_6245295
  have hstable : (prefixWord ++ tailWord_6245295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245295).length < 2 ^ (prefixWord ++ tailWord_6245295).sum := by decide
  have hdescent : baseEnd_6245295 < baseStart_6245295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245298 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6245298 : Nat := 118140960795 + 6245298 * 2 ^ 59
def prefixEnd_6245298 : Nat := 4983230072969 + 3 ^ 40 * 6245298 * 2
def baseEnd_6245298 : Nat := 3206839704563211476553403

theorem tailTrace_6245298 : CollatzResearch.WordTrace tailWord_6245298 prefixEnd_6245298 3206839704563211476553403 := by
  unfold tailWord_6245298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56946182832089858206548137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151856487552239621884128365 56946182832089858206548137)
  ·
    refine ⟨42709637124067393654911103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56946182832089858206548137 42709637124067393654911103)
    ·
      refine ⟨64064455686101090482366655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42709637124067393654911103 64064455686101090482366655)
      ·
        refine ⟨96096683529151635723549983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64064455686101090482366655 96096683529151635723549983)
        ·
          refine ⟨144145025293727453585324975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96096683529151635723549983 144145025293727453585324975)
          ·
            refine ⟨216217537940591180377987463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144145025293727453585324975 216217537940591180377987463)
            ·
              refine ⟨324326306910886770566981195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216217537940591180377987463 324326306910886770566981195)
              ·
                refine ⟨486489460366330155850471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324326306910886770566981195 486489460366330155850471793)
                ·
                  refine ⟨364867095274747616887853845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486489460366330155850471793 364867095274747616887853845)
                  ·
                    refine ⟨17103145091003794541618149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 364867095274747616887853845 17103145091003794541618149)
                    ·
                      refine ⟨3206839704563211476553403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17103145091003794541618149 3206839704563211476553403)
                      ·
                        rfl

theorem cell23_6245298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6245298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245298 prefixEnd_6245298 := by exact prefixLift 6245298
  have htrace : WordTrace (prefixWord ++ tailWord_6245298) baseStart_6245298 baseEnd_6245298 := by
    simpa [prefixWord, tailWord_6245298, baseEnd_6245298] using wordTrace_append hprefix tailTrace_6245298
  have hstable : (prefixWord ++ tailWord_6245298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245298).length < 2 ^ (prefixWord ++ tailWord_6245298).sum := by decide
  have hdescent : baseEnd_6245298 < baseStart_6245298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245305 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6245305 : Nat := 118140960795 + 6245305 * 2 ^ 59
def prefixEnd_6245305 : Nat := 4983230072969 + 3 ^ 40 * 6245305 * 2
def baseEnd_6245305 : Nat := 3206843298927792949165871

theorem tailTrace_6245305 : CollatzResearch.WordTrace tailWord_6245305 prefixEnd_6245305 3206843298927792949165871 := by
  unfold tailWord_6245305
  simp only [CollatzResearch.WordTrace]
  refine ⟨227784986639334073021697369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151856657759556048681131579 227784986639334073021697369)
  ·
    refine ⟨170838739979500554766273027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227784986639334073021697369 170838739979500554766273027)
    ·
      refine ⟨256258109969250832149409541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170838739979500554766273027 256258109969250832149409541)
      ·
        refine ⟨48048395619234531028014289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256258109969250832149409541 48048395619234531028014289)
        ·
          refine ⟨36036296714425898271010717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48048395619234531028014289 36036296714425898271010717)
          ·
            refine ⟨13513611267909711851629019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36036296714425898271010717 13513611267909711851629019)
            ·
              refine ⟨20270416901864567777443529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13513611267909711851629019 20270416901864567777443529)
              ·
                refine ⟨15202812676398425833082647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20270416901864567777443529 15202812676398425833082647)
                ·
                  refine ⟨22804219014597638749623971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15202812676398425833082647 22804219014597638749623971)
                  ·
                    refine ⟨34206328521896458124435957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22804219014597638749623971 34206328521896458124435957)
                    ·
                      refine ⟨3206843298927792949165871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34206328521896458124435957 3206843298927792949165871)
                      ·
                        rfl

theorem cell23_6245305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6245305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245305 prefixEnd_6245305 := by exact prefixLift 6245305
  have htrace : WordTrace (prefixWord ++ tailWord_6245305) baseStart_6245305 baseEnd_6245305 := by
    simpa [prefixWord, tailWord_6245305, baseEnd_6245305] using wordTrace_append hprefix tailTrace_6245305
  have hstable : (prefixWord ++ tailWord_6245305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245305).length < 2 ^ (prefixWord ++ tailWord_6245305).sum := by decide
  have hdescent : baseEnd_6245305 < baseStart_6245305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245336 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_6245336 : Nat := 118140960795 + 6245336 * 2 ^ 59
def prefixEnd_6245336 : Nat := 4983230072969 + 3 ^ 40 * 6245336 * 2
def baseEnd_6245336 : Nat := 3206859216828082327878229

theorem tailTrace_6245336 : CollatzResearch.WordTrace tailWord_6245336 prefixEnd_6245336 3206859216828082327878229 := by
  unfold tailWord_6245336
  simp only [CollatzResearch.WordTrace]
  refine ⟨113893058651110882658037931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151857411534814510210717241 113893058651110882658037931)
  ·
    refine ⟨170839587976666323987056897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113893058651110882658037931 170839587976666323987056897)
    ·
      refine ⟨128129690982499742990292673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170839587976666323987056897 128129690982499742990292673)
      ·
        refine ⟨96097268236874807242719505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128129690982499742990292673 96097268236874807242719505)
        ·
          refine ⟨72072951177656105432039629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96097268236874807242719505 72072951177656105432039629)
          ·
            refine ⟨27027356691621039537014861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72072951177656105432039629 27027356691621039537014861)
            ·
              refine ⟨10135258759357889826380573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27027356691621039537014861 10135258759357889826380573)
              ·
                refine ⟨3800722034759208684892715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10135258759357889826380573 3800722034759208684892715)
                ·
                  refine ⟨5701083052138813027339073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800722034759208684892715 5701083052138813027339073)
                  ·
                    refine ⟨4275812289104109770504305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701083052138813027339073 4275812289104109770504305)
                    ·
                      refine ⟨3206859216828082327878229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4275812289104109770504305 3206859216828082327878229)
                      ·
                        rfl

theorem cell23_6245336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_6245336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245336 prefixEnd_6245336 := by exact prefixLift 6245336
  have htrace : WordTrace (prefixWord ++ tailWord_6245336) baseStart_6245336 baseEnd_6245336 := by
    simpa [prefixWord, tailWord_6245336, baseEnd_6245336] using wordTrace_append hprefix tailTrace_6245336
  have hstable : (prefixWord ++ tailWord_6245336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245336).length < 2 ^ (prefixWord ++ tailWord_6245336).sum := by decide
  have hdescent : baseEnd_6245336 < baseStart_6245336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245352 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6245352 : Nat := 118140960795 + 6245352 * 2 ^ 59
def prefixEnd_6245352 : Nat := 4983230072969 + 3 ^ 40 * 6245352 * 2
def baseEnd_6245352 : Nat := 3206867432518554265278155

theorem tailTrace_6245352 : CollatzResearch.WordTrace tailWord_6245352 prefixEnd_6245352 3206867432518554265278155 := by
  unfold tailWord_6245352
  simp only [CollatzResearch.WordTrace]
  refine ⟨113893350435081900024329155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151857800580109200032438873 113893350435081900024329155)
  ·
    refine ⟨170840025652622850036493733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113893350435081900024329155 170840025652622850036493733)
    ·
      refine ⟨32032504809866784381842575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170840025652622850036493733 32032504809866784381842575)
      ·
        refine ⟨48048757214800176572763863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032504809866784381842575 48048757214800176572763863)
        ·
          refine ⟨72073135822200264859145795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48048757214800176572763863 72073135822200264859145795)
          ·
            refine ⟨108109703733300397288718693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72073135822200264859145795 108109703733300397288718693)
            ·
              refine ⟨20270569449993824491634755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108109703733300397288718693 20270569449993824491634755)
              ·
                refine ⟨30405854174990736737452133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20270569449993824491634755 30405854174990736737452133)
                ·
                  refine ⟨5701097657810763138272275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30405854174990736737452133 5701097657810763138272275)
                  ·
                    refine ⟨8551646486716144707408413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5701097657810763138272275 8551646486716144707408413)
                    ·
                      refine ⟨3206867432518554265278155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551646486716144707408413 3206867432518554265278155)
                      ·
                        rfl

theorem cell23_6245352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6245352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245352 prefixEnd_6245352 := by exact prefixLift 6245352
  have htrace : WordTrace (prefixWord ++ tailWord_6245352) baseStart_6245352 baseEnd_6245352 := by
    simpa [prefixWord, tailWord_6245352, baseEnd_6245352] using wordTrace_append hprefix tailTrace_6245352
  have hstable : (prefixWord ++ tailWord_6245352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245352).length < 2 ^ (prefixWord ++ tailWord_6245352).sum := by decide
  have hdescent : baseEnd_6245352 < baseStart_6245352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245368 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_6245368 : Nat := 118140960795 + 6245368 * 2 ^ 59
def prefixEnd_6245368 : Nat := 4983230072969 + 3 ^ 40 * 6245368 * 2
def baseEnd_6245368 : Nat := 1068958549403008734226027

theorem tailTrace_6245368 : CollatzResearch.WordTrace tailWord_6245368 prefixEnd_6245368 1068958549403008734226027 := by
  unfold tailWord_6245368
  simp only [CollatzResearch.WordTrace]
  refine ⟨113893642219052917390620379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151858189625403889854160505 113893642219052917390620379)
  ·
    refine ⟨170840463328579376085930569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113893642219052917390620379 170840463328579376085930569)
    ·
      refine ⟨128130347496434532064447927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170840463328579376085930569 128130347496434532064447927)
      ·
        refine ⟨192195521244651798096671891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128130347496434532064447927 192195521244651798096671891)
        ·
          refine ⟨288293281866977697145007837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192195521244651798096671891 288293281866977697145007837)
          ·
            refine ⟨108109980700116636429377939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288293281866977697145007837 108109980700116636429377939)
            ·
              refine ⟨162164971050174954644066909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108109980700116636429377939 162164971050174954644066909)
              ·
                refine ⟨60811864143815607991525091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162164971050174954644066909 60811864143815607991525091)
                ·
                  refine ⟨91217796215723411987287637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60811864143815607991525091 91217796215723411987287637)
                  ·
                    refine ⟨1068958549403008734226027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91217796215723411987287637 1068958549403008734226027)
                    ·
                      rfl

theorem cell23_6245368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_6245368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245368 prefixEnd_6245368 := by exact prefixLift 6245368
  have htrace : WordTrace (prefixWord ++ tailWord_6245368) baseStart_6245368 baseEnd_6245368 := by
    simpa [prefixWord, tailWord_6245368, baseEnd_6245368] using wordTrace_append hprefix tailTrace_6245368
  have hstable : (prefixWord ++ tailWord_6245368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245368).length < 2 ^ (prefixWord ++ tailWord_6245368).sum := by decide
  have hdescent : baseEnd_6245368 < baseStart_6245368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245412 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6245412 : Nat := 118140960795 + 6245412 * 2 ^ 59
def prefixEnd_6245412 : Nat := 4983230072969 + 3 ^ 40 * 6245412 * 2
def baseEnd_6245412 : Nat := 3206898241357824030527879

theorem tailTrace_6245412 : CollatzResearch.WordTrace tailWord_6245412 prefixEnd_6245412 3206898241357824030527879 := by
  unfold tailWord_6245412
  simp only [CollatzResearch.WordTrace]
  refine ⟨113894444624973215147921245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151859259499964286863894993 113894444624973215147921245)
  ·
    refine ⟨42710416734364955680470467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113894444624973215147921245 42710416734364955680470467)
    ·
      refine ⟨64065625101547433520705701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42710416734364955680470467 64065625101547433520705701)
      ·
        refine ⟨12012304706540143785132319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64065625101547433520705701 12012304706540143785132319)
        ·
          refine ⟨18018457059810215677698479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012304706540143785132319 18018457059810215677698479)
          ·
            refine ⟨27027685589715323516547719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018457059810215677698479 27027685589715323516547719)
            ·
              refine ⟨40541528384572985274821579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27027685589715323516547719 40541528384572985274821579)
              ·
                refine ⟨60812292576859477912232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40541528384572985274821579 60812292576859477912232369)
                ·
                  refine ⟨45609219432644608434174277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60812292576859477912232369 45609219432644608434174277)
                  ·
                    refine ⟨8551728643620864081407677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45609219432644608434174277 8551728643620864081407677)
                    ·
                      refine ⟨3206898241357824030527879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8551728643620864081407677 3206898241357824030527879)
                      ·
                        rfl

theorem cell23_6245412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6245412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245412 prefixEnd_6245412 := by exact prefixLift 6245412
  have htrace : WordTrace (prefixWord ++ tailWord_6245412) baseStart_6245412 baseEnd_6245412 := by
    simpa [prefixWord, tailWord_6245412, baseEnd_6245412] using wordTrace_append hprefix tailTrace_6245412
  have hstable : (prefixWord ++ tailWord_6245412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245412).length < 2 ^ (prefixWord ++ tailWord_6245412).sum := by decide
  have hdescent : baseEnd_6245412 < baseStart_6245412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245422 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6245422 : Nat := 118140960795 + 6245422 * 2 ^ 59
def prefixEnd_6245422 : Nat := 4983230072969 + 3 ^ 40 * 6245422 * 2
def baseEnd_6245422 : Nat := 3206903376164368991402833

theorem tailTrace_6245422 : CollatzResearch.WordTrace tailWord_6245422 prefixEnd_6245422 3206903376164368991402833 := by
  unfold tailWord_6245422
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473656747488775250463315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151859502653273468002471013 28473656747488775250463315)
  ·
    refine ⟨42710485121233162875694973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28473656747488775250463315 42710485121233162875694973)
    ·
      refine ⟨16016431920462436078385615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42710485121233162875694973 16016431920462436078385615)
      ·
        refine ⟨24024647880693654117578423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16016431920462436078385615 24024647880693654117578423)
        ·
          refine ⟨36036971821040481176367635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24024647880693654117578423 36036971821040481176367635)
          ·
            refine ⟨54055457731560721764551453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36036971821040481176367635 54055457731560721764551453)
            ·
              refine ⟨20270796649335270661706795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54055457731560721764551453 20270796649335270661706795)
              ·
                refine ⟨30406194974002905992560193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20270796649335270661706795 30406194974002905992560193)
                ·
                  refine ⟨22804646230502179494420145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30406194974002905992560193 22804646230502179494420145)
                  ·
                    refine ⟨17103484672876634620815109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22804646230502179494420145 17103484672876634620815109)
                    ·
                      refine ⟨3206903376164368991402833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17103484672876634620815109 3206903376164368991402833)
                      ·
                        rfl

theorem cell23_6245422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6245422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245422 prefixEnd_6245422 := by exact prefixLift 6245422
  have htrace : WordTrace (prefixWord ++ tailWord_6245422) baseStart_6245422 baseEnd_6245422 := by
    simpa [prefixWord, tailWord_6245422, baseEnd_6245422] using wordTrace_append hprefix tailTrace_6245422
  have hstable : (prefixWord ++ tailWord_6245422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245422).length < 2 ^ (prefixWord ++ tailWord_6245422).sum := by decide
  have hdescent : baseEnd_6245422 < baseStart_6245422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245482 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6245482 : Nat := 118140960795 + 6245482 * 2 ^ 59
def prefixEnd_6245482 : Nat := 4983230072969 + 3 ^ 40 * 6245482 * 2
def baseEnd_6245482 : Nat := 3206934185003638756652557

theorem tailTrace_6245482 : CollatzResearch.WordTrace tailWord_6245482 prefixEnd_6245482 3206934185003638756652557 := by
  unfold tailWord_6245482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56947860589923208062722675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151860961573128554833927133 56947860589923208062722675)
  ·
    refine ⟨85421790884884812094084013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56947860589923208062722675 85421790884884812094084013)
    ·
      refine ⟨32033171581831804535281505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85421790884884812094084013 32033171581831804535281505)
      ·
        refine ⟨24024878686373853401461129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32033171581831804535281505 24024878686373853401461129)
        ·
          refine ⟨18018659014780390051095847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24024878686373853401461129 18018659014780390051095847)
          ·
            refine ⟨27027988522170585076643771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018659014780390051095847 27027988522170585076643771)
            ·
              refine ⟨40541982783255877614965657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27027988522170585076643771 40541982783255877614965657)
              ·
                refine ⟨30406487087441908211224243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40541982783255877614965657 30406487087441908211224243)
                ·
                  refine ⟨45609730631162862316836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30406487087441908211224243 45609730631162862316836365)
                  ·
                    refine ⟨17103648986686073368813637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45609730631162862316836365 17103648986686073368813637)
                    ·
                      refine ⟨3206934185003638756652557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17103648986686073368813637 3206934185003638756652557)
                      ·
                        rfl

theorem cell23_6245482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6245482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245482 prefixEnd_6245482 := by exact prefixLift 6245482
  have htrace : WordTrace (prefixWord ++ tailWord_6245482) baseStart_6245482 baseEnd_6245482 := by
    simpa [prefixWord, tailWord_6245482, baseEnd_6245482] using wordTrace_append hprefix tailTrace_6245482
  have hstable : (prefixWord ++ tailWord_6245482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245482).length < 2 ^ (prefixWord ++ tailWord_6245482).sum := by decide
  have hdescent : baseEnd_6245482 < baseStart_6245482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245495 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_6245495 : Nat := 118140960795 + 6245495 * 2 ^ 59
def prefixEnd_6245495 : Nat := 4983230072969 + 3 ^ 40 * 6245495 * 2
def baseEnd_6245495 : Nat := 3206940860252147205789997

theorem tailTrace_6245495 : CollatzResearch.WordTrace tailWord_6245495 prefixEnd_6245495 3206940860252147205789997 := by
  unfold tailWord_6245495
  simp only [CollatzResearch.WordTrace]
  refine ⟨227791916508645735471113939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151861277672430490314075959 227791916508645735471113939)
  ·
    refine ⟨341687874762968603206670909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227791916508645735471113939 341687874762968603206670909)
    ·
      refine ⟨128132953036113226202501591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341687874762968603206670909 128132953036113226202501591)
      ·
        refine ⟨192199429554169839303752387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128132953036113226202501591 192199429554169839303752387)
        ·
          refine ⟨288299144331254758955628581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192199429554169839303752387 288299144331254758955628581)
          ·
            refine ⟨54056089562110267304180359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288299144331254758955628581 54056089562110267304180359)
            ·
              refine ⟨81084134343165400956270539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54056089562110267304180359 81084134343165400956270539)
              ·
                refine ⟨121626201514748101434405809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81084134343165400956270539 121626201514748101434405809)
                ·
                  refine ⟨91219651136061076075804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121626201514748101434405809 91219651136061076075804357)
                  ·
                    refine ⟨17103684588011451764213317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91219651136061076075804357 17103684588011451764213317)
                    ·
                      refine ⟨3206940860252147205789997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17103684588011451764213317 3206940860252147205789997)
                      ·
                        rfl

theorem cell23_6245495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_6245495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245495 prefixEnd_6245495 := by exact prefixLift 6245495
  have htrace : WordTrace (prefixWord ++ tailWord_6245495) baseStart_6245495 baseEnd_6245495 := by
    simpa [prefixWord, tailWord_6245495, baseEnd_6245495] using wordTrace_append hprefix tailTrace_6245495
  have hstable : (prefixWord ++ tailWord_6245495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245495).length < 2 ^ (prefixWord ++ tailWord_6245495).sum := by decide
  have hdescent : baseEnd_6245495 < baseStart_6245495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245522 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_6245522 : Nat := 118140960795 + 6245522 * 2 ^ 59
def prefixEnd_6245522 : Nat := 4983230072969 + 3 ^ 40 * 6245522 * 2
def baseEnd_6245522 : Nat := 356328302692202066683597

theorem tailTrace_6245522 : CollatzResearch.WordTrace tailWord_6245522 prefixEnd_6245522 356328302692202066683597 := by
  unfold tailWord_6245522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56948225319886979770586705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151861934186365279388231213 56948225319886979770586705)
  ·
    refine ⟨42711168989915234827940029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56948225319886979770586705 42711168989915234827940029)
    ·
      refine ⟨16016688371218213060477511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42711168989915234827940029 16016688371218213060477511)
      ·
        refine ⟨24025032556827319590716267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16016688371218213060477511 24025032556827319590716267)
        ·
          refine ⟨36037548835240979386074401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24025032556827319590716267 36037548835240979386074401)
          ·
            refine ⟨27028161626430734539555801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36037548835240979386074401 27028161626430734539555801)
            ·
              refine ⟨20271121219823050904666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27028161626430734539555801 20271121219823050904666851)
              ·
                refine ⟨30406681829734576357000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20271121219823050904666851 30406681829734576357000277)
                ·
                  refine ⟨356328302692202066683597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30406681829734576357000277 356328302692202066683597)
                  ·
                    rfl

theorem cell23_6245522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_6245522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245522 prefixEnd_6245522 := by exact prefixLift 6245522
  have htrace : WordTrace (prefixWord ++ tailWord_6245522) baseStart_6245522 baseEnd_6245522 := by
    simpa [prefixWord, tailWord_6245522, baseEnd_6245522] using wordTrace_append hprefix tailTrace_6245522
  have hstable : (prefixWord ++ tailWord_6245522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245522).length < 2 ^ (prefixWord ++ tailWord_6245522).sum := by decide
  have hdescent : baseEnd_6245522 < baseStart_6245522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245525 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6245525 : Nat := 118140960795 + 6245525 * 2 ^ 59
def prefixEnd_6245525 : Nat := 4983230072969 + 3 ^ 40 * 6245525 * 2
def baseEnd_6245525 : Nat := 3206956264671782088414859

theorem tailTrace_6245525 : CollatzResearch.WordTrace tailWord_6245525 prefixEnd_6245525 3206956264671782088414859 := by
  unfold tailWord_6245525
  simp only [CollatzResearch.WordTrace]
  refine ⟨227793010698537050594706029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151862007132358033729804019 227793010698537050594706029)
  ·
    refine ⟨85422379011951393973014761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227793010698537050594706029 85422379011951393973014761)
    ·
      refine ⟨64066784258963545479761071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85422379011951393973014761 64066784258963545479761071)
      ·
        refine ⟨96100176388445318219641607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64066784258963545479761071 96100176388445318219641607)
        ·
          refine ⟨144150264582667977329462411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96100176388445318219641607 144150264582667977329462411)
          ·
            refine ⟨216225396874001965994193617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144150264582667977329462411 216225396874001965994193617)
            ·
              refine ⟨162169047655501474495645213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216225396874001965994193617 162169047655501474495645213)
              ·
                refine ⟨60813392870813052935866955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162169047655501474495645213 60813392870813052935866955)
                ·
                  refine ⟨91220089306219579403800433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60813392870813052935866955 91220089306219579403800433)
                  ·
                    refine ⟨68415066979664684552850325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91220089306219579403800433 68415066979664684552850325)
                    ·
                      refine ⟨3206956264671782088414859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68415066979664684552850325 3206956264671782088414859)
                      ·
                        rfl

theorem cell23_6245525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6245525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245525 prefixEnd_6245525 := by exact prefixLift 6245525
  have htrace : WordTrace (prefixWord ++ tailWord_6245525) baseStart_6245525 baseEnd_6245525 := by
    simpa [prefixWord, tailWord_6245525, baseEnd_6245525] using wordTrace_append hprefix tailTrace_6245525
  have hstable : (prefixWord ++ tailWord_6245525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245525).length < 2 ^ (prefixWord ++ tailWord_6245525).sum := by decide
  have hdescent : baseEnd_6245525 < baseStart_6245525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245589 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6245589 : Nat := 118140960795 + 6245589 * 2 ^ 59
def prefixEnd_6245589 : Nat := 4983230072969 + 3 ^ 40 * 6245589 * 2
def baseEnd_6245589 : Nat := 3206989127433669838014565

theorem tailTrace_6245589 : CollatzResearch.WordTrace tailWord_6245589 prefixEnd_6245589 3206989127433669838014565 := by
  unfold tailWord_6245589
  simp only [CollatzResearch.WordTrace]
  refine ⟨227795344970305189525035821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151863563313536793016690547 227795344970305189525035821)
  ·
    refine ⟨85423254363864446071888433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227795344970305189525035821 85423254363864446071888433)
    ·
      refine ⟨64067440772898334553916325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85423254363864446071888433 64067440772898334553916325)
      ·
        refine ⟨12012645144918437728859311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64067440772898334553916325 12012645144918437728859311)
        ·
          refine ⟨18018967717377656593288967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012645144918437728859311 18018967717377656593288967)
          ·
            refine ⟨27028451576066484889933451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018967717377656593288967 27028451576066484889933451)
            ·
              refine ⟨40542677364099727334900177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27028451576066484889933451 40542677364099727334900177)
              ·
                refine ⟨30407008023074795501175133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40542677364099727334900177 30407008023074795501175133)
                ·
                  refine ⟨11402628008653048312940675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30407008023074795501175133 11402628008653048312940675)
                  ·
                    refine ⟨17103942012979572469411013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11402628008653048312940675 17103942012979572469411013)
                    ·
                      refine ⟨3206989127433669838014565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17103942012979572469411013 3206989127433669838014565)
                      ·
                        rfl

theorem cell23_6245589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6245589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245589 prefixEnd_6245589 := by exact prefixLift 6245589
  have htrace : WordTrace (prefixWord ++ tailWord_6245589) baseStart_6245589 baseEnd_6245589 := by
    simpa [prefixWord, tailWord_6245589, baseEnd_6245589] using wordTrace_append hprefix tailTrace_6245589
  have hstable : (prefixWord ++ tailWord_6245589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245589).length < 2 ^ (prefixWord ++ tailWord_6245589).sum := by decide
  have hdescent : baseEnd_6245589 < baseStart_6245589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245599 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 2, 4]
def baseStart_6245599 : Nat := 118140960795 + 6245599 * 2 ^ 59
def prefixEnd_6245599 : Nat := 4983230072969 + 3 ^ 40 * 6245599 * 2
def baseEnd_6245599 : Nat := 1068998087413404932963173

theorem tailTrace_6245599 : CollatzResearch.WordTrace tailWord_6245599 prefixEnd_6245599 1068998087413404932963173 := by
  unfold tailWord_6245599
  simp only [CollatzResearch.WordTrace]
  refine ⟨227795709700268961232899851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151863806466845974155266567 227795709700268961232899851)
  ·
    refine ⟨341693564550403441849349777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227795709700268961232899851 341693564550403441849349777)
    ·
      refine ⟨256270173412802581387012333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341693564550403441849349777 256270173412802581387012333)
      ·
        refine ⟨96101315029800968020129625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256270173412802581387012333 96101315029800968020129625)
        ·
          refine ⟨72075986272350726015097219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96101315029800968020129625 72075986272350726015097219)
          ·
            refine ⟨108113979408526089022645829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72075986272350726015097219 108113979408526089022645829)
            ·
              refine ⟨20271371139098641691746093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108113979408526089022645829 20271371139098641691746093)
              ·
                refine ⟨7601764177161990634404785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20271371139098641691746093 7601764177161990634404785)
                ·
                  refine ⟨5701323132871492975803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601764177161990634404785 5701323132871492975803589)
                  ·
                    refine ⟨1068998087413404932963173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701323132871492975803589 1068998087413404932963173)
                    ·
                      rfl

theorem cell23_6245599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_6245599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245599 prefixEnd_6245599 := by exact prefixLift 6245599
  have htrace : WordTrace (prefixWord ++ tailWord_6245599) baseStart_6245599 baseEnd_6245599 := by
    simpa [prefixWord, tailWord_6245599, baseEnd_6245599] using wordTrace_append hprefix tailTrace_6245599
  have hstable : (prefixWord ++ tailWord_6245599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245599).length < 2 ^ (prefixWord ++ tailWord_6245599).sum := by decide
  have hdescent : baseEnd_6245599 < baseStart_6245599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245620 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6245620 : Nat := 118140960795 + 6245620 * 2 ^ 59
def prefixEnd_6245620 : Nat := 4983230072969 + 3 ^ 40 * 6245620 * 2
def baseEnd_6245620 : Nat := 1069001681777986405575641

theorem tailTrace_6245620 : CollatzResearch.WordTrace tailWord_6245620 prefixEnd_6245620 1069001681777986405575641 := by
  unfold tailWord_6245620
  simp only [CollatzResearch.WordTrace]
  refine ⟨113898237816596440909707157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151864317088795254546276209 113898237816596440909707157)
  ·
    refine ⟨5338979897652958167642523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113898237816596440909707157 5338979897652958167642523)
    ·
      refine ⟨8008469846479437251463785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338979897652958167642523 8008469846479437251463785)
      ·
        refine ⟨6006352384859577938597839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008469846479437251463785 6006352384859577938597839)
        ·
          refine ⟨9009528577289366907896759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006352384859577938597839 9009528577289366907896759)
          ·
            refine ⟨13514292865934050361845139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9009528577289366907896759 13514292865934050361845139)
            ·
              refine ⟨20271439298901075542767709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13514292865934050361845139 20271439298901075542767709)
              ·
                refine ⟨7601789737087903328537891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20271439298901075542767709 7601789737087903328537891)
                ·
                  refine ⟨11402684605631854992806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7601789737087903328537891 11402684605631854992806837)
                  ·
                    refine ⟨1069001681777986405575641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11402684605631854992806837 1069001681777986405575641)
                    ·
                      rfl

theorem cell23_6245620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6245620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245620 prefixEnd_6245620 := by exact prefixLift 6245620
  have htrace : WordTrace (prefixWord ++ tailWord_6245620) baseStart_6245620 baseEnd_6245620 := by
    simpa [prefixWord, tailWord_6245620, baseEnd_6245620] using wordTrace_append hprefix tailTrace_6245620
  have hstable : (prefixWord ++ tailWord_6245620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245620).length < 2 ^ (prefixWord ++ tailWord_6245620).sum := by decide
  have hdescent : baseEnd_6245620 < baseStart_6245620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245650 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6245650 : Nat := 118140960795 + 6245650 * 2 ^ 59
def prefixEnd_6245650 : Nat := 4983230072969 + 3 ^ 40 * 6245650 * 2
def baseEnd_6245650 : Nat := 1069006816584531366450595

theorem tailTrace_6245650 : CollatzResearch.WordTrace tailWord_6245650 prefixEnd_6245650 1069006816584531366450595 := by
  unfold tailWord_6245650
  simp only [CollatzResearch.WordTrace]
  refine ⟨56949392455771049235751601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151865046548722797962004269 56949392455771049235751601)
  ·
    refine ⟨42712044341828286926813701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56949392455771049235751601 42712044341828286926813701)
    ·
      refine ⟨8008508314092803798777569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42712044341828286926813701 8008508314092803798777569)
      ·
        refine ⟨6006381235569602849083177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008508314092803798777569 6006381235569602849083177)
        ·
          refine ⟨4504785926677202136812383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006381235569602849083177 4504785926677202136812383)
          ·
            refine ⟨6757178890015803205218575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504785926677202136812383 6757178890015803205218575)
            ·
              refine ⟨10135768335023704807827863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757178890015803205218575 10135768335023704807827863)
              ·
                refine ⟨15203652502535557211741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135768335023704807827863 15203652502535557211741795)
                ·
                  refine ⟨22805478753803335817612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15203652502535557211741795 22805478753803335817612693)
                  ·
                    refine ⟨1069006816584531366450595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22805478753803335817612693 1069006816584531366450595)
                    ·
                      rfl

theorem cell23_6245650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6245650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245650 prefixEnd_6245650 := by exact prefixLift 6245650
  have htrace : WordTrace (prefixWord ++ tailWord_6245650) baseStart_6245650 baseEnd_6245650 := by
    simpa [prefixWord, tailWord_6245650, baseEnd_6245650] using wordTrace_append hprefix tailTrace_6245650
  have hstable : (prefixWord ++ tailWord_6245650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245650).length < 2 ^ (prefixWord ++ tailWord_6245650).sum := by decide
  have hdescent : baseEnd_6245650 < baseStart_6245650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245656 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6245656 : Nat := 118140960795 + 6245656 * 2 ^ 59
def prefixEnd_6245656 : Nat := 4983230072969 + 3 ^ 40 * 6245656 * 2
def baseEnd_6245656 : Nat := 3207023530637521075876757

theorem tailTrace_6245656 : CollatzResearch.WordTrace tailWord_6245656 prefixEnd_6245656 3207023530637521075876757 := by
  unfold tailWord_6245656
  simp only [CollatzResearch.WordTrace]
  refine ⟨113898894330531229983862411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151865192440708306645149881 113898894330531229983862411)
  ·
    refine ⟨170848341495796844975793617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113898894330531229983862411 170848341495796844975793617)
    ·
      refine ⟨128136256121847633731845213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170848341495796844975793617 128136256121847633731845213)
      ·
        refine ⟨48051096045692862649441955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128136256121847633731845213 48051096045692862649441955)
        ·
          refine ⟨72076644068539293974162933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48051096045692862649441955 72076644068539293974162933)
          ·
            refine ⟨6757185381425558810077775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72076644068539293974162933 6757185381425558810077775)
            ·
              refine ⟨10135778072138338215116663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757185381425558810077775 10135778072138338215116663)
              ·
                refine ⟨15203667108207507322674995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135778072138338215116663 15203667108207507322674995)
                ·
                  refine ⟨22805500662311260984012493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15203667108207507322674995 22805500662311260984012493)
                  ·
                    refine ⟨8552062748366722869004685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22805500662311260984012493 8552062748366722869004685)
                    ·
                      refine ⟨3207023530637521075876757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8552062748366722869004685 3207023530637521075876757)
                      ·
                        rfl

theorem cell23_6245656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6245656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245656 prefixEnd_6245656 := by exact prefixLift 6245656
  have htrace : WordTrace (prefixWord ++ tailWord_6245656) baseStart_6245656 baseEnd_6245656 := by
    simpa [prefixWord, tailWord_6245656, baseEnd_6245656] using wordTrace_append hprefix tailTrace_6245656
  have hstable : (prefixWord ++ tailWord_6245656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245656).length < 2 ^ (prefixWord ++ tailWord_6245656).sum := by decide
  have hdescent : baseEnd_6245656 < baseStart_6245656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245679 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 4, 2]
def baseStart_6245679 : Nat := 118140960795 + 6245679 * 2 ^ 59
def prefixEnd_6245679 : Nat := 4983230072969 + 3 ^ 40 * 6245679 * 2
def baseEnd_6245679 : Nat := 3207035340692574485889151

theorem tailTrace_6245679 : CollatzResearch.WordTrace tailWord_6245679 prefixEnd_6245679 3207035340692574485889151 := by
  unfold tailWord_6245679
  simp only [CollatzResearch.WordTrace]
  refine ⟨227798627539979134895812091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151865751693319423263874727 227798627539979134895812091)
  ·
    refine ⟨341697941309968702343718137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227798627539979134895812091 341697941309968702343718137)
    ·
      refine ⟨256273455982476526757788603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341697941309968702343718137 256273455982476526757788603)
      ·
        refine ⟨384410183973714790136682905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256273455982476526757788603 384410183973714790136682905)
        ·
          refine ⟨288307637980286092602512179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384410183973714790136682905 288307637980286092602512179)
          ·
            refine ⟨432461456970429138903768269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288307637980286092602512179 432461456970429138903768269)
            ·
              refine ⟨162173046363910927088913101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432461456970429138903768269 162173046363910927088913101)
              ·
                refine ⟨60814892386466597658342413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162173046363910927088913101 60814892386466597658342413)
                ·
                  refine ⟨22805584644924974121878405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60814892386466597658342413 22805584644924974121878405)
                  ·
                    refine ⟨4276047120923432647852201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22805584644924974121878405 4276047120923432647852201)
                    ·
                      refine ⟨3207035340692574485889151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276047120923432647852201 3207035340692574485889151)
                      ·
                        rfl

theorem cell23_6245679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4, 2].length) (baseStart_6245679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245679 prefixEnd_6245679 := by exact prefixLift 6245679
  have htrace : WordTrace (prefixWord ++ tailWord_6245679) baseStart_6245679 baseEnd_6245679 := by
    simpa [prefixWord, tailWord_6245679, baseEnd_6245679] using wordTrace_append hprefix tailTrace_6245679
  have hstable : (prefixWord ++ tailWord_6245679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245679).length < 2 ^ (prefixWord ++ tailWord_6245679).sum := by decide
  have hdescent : baseEnd_6245679 < baseStart_6245679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245696 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2]
def baseStart_6245696 : Nat := 118140960795 + 6245696 * 2 ^ 59
def prefixEnd_6245696 : Nat := 4983230072969 + 3 ^ 40 * 6245696 * 2
def baseEnd_6245696 : Nat := 3207044069863700919376573

theorem tailTrace_6245696 : CollatzResearch.WordTrace tailWord_6245696 prefixEnd_6245696 3207044069863700919376573 := by
  unfold tailWord_6245696
  simp only [CollatzResearch.WordTrace]
  refine ⟨113899623790458773399590471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151866165053945031199453961 113899623790458773399590471)
  ·
    refine ⟨170849435685688160099385707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113899623790458773399590471 170849435685688160099385707)
    ·
      refine ⟨256274153528532240149078561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170849435685688160099385707 256274153528532240149078561)
      ·
        refine ⟨192205615146399180111808921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256274153528532240149078561 192205615146399180111808921)
        ·
          refine ⟨144154211359799385083856691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192205615146399180111808921 144154211359799385083856691)
          ·
            refine ⟨216231317039699077625785037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144154211359799385083856691 216231317039699077625785037)
            ·
              refine ⟨81086743889887154109669389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216231317039699077625785037 81086743889887154109669389)
              ·
                refine ⟨30407528958707682791126021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81086743889887154109669389 30407528958707682791126021)
                ·
                  refine ⟨5701411679757690523336129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30407528958707682791126021 5701411679757690523336129)
                  ·
                    refine ⟨4276058759818267892502097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701411679757690523336129 4276058759818267892502097)
                    ·
                      refine ⟨3207044069863700919376573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276058759818267892502097 3207044069863700919376573)
                      ·
                        rfl

theorem cell23_6245696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_6245696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245696 prefixEnd_6245696 := by exact prefixLift 6245696
  have htrace : WordTrace (prefixWord ++ tailWord_6245696) baseStart_6245696 baseEnd_6245696 := by
    simpa [prefixWord, tailWord_6245696, baseEnd_6245696] using wordTrace_append hprefix tailTrace_6245696
  have hstable : (prefixWord ++ tailWord_6245696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245696).length < 2 ^ (prefixWord ++ tailWord_6245696).sum := by decide
  have hdescent : baseEnd_6245696 < baseStart_6245696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245713 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_6245713 : Nat := 118140960795 + 6245713 * 2 ^ 59
def prefixEnd_6245713 : Nat := 4983230072969 + 3 ^ 40 * 6245713 * 2
def baseEnd_6245713 : Nat := 3207052799034827352863995

theorem tailTrace_6245713 : CollatzResearch.WordTrace tailWord_6245713 prefixEnd_6245713 3207052799034827352863995 := by
  unfold tailWord_6245713
  simp only [CollatzResearch.WordTrace]
  refine ⟨227799867621855958702549793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151866578414570639135033195 227799867621855958702549793)
  ·
    refine ⟨170849900716391969026912345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227799867621855958702549793 170849900716391969026912345)
    ·
      refine ⟨128137425537293976770184259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170849900716391969026912345 128137425537293976770184259)
      ·
        refine ⟨192206138305940965155276389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128137425537293976770184259 192206138305940965155276389)
        ·
          refine ⟨36038650932363930966614323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192206138305940965155276389 36038650932363930966614323)
          ·
            refine ⟨54057976398545896449921485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36038650932363930966614323 54057976398545896449921485)
            ·
              refine ⟨20271741149454711168720557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54057976398545896449921485 20271741149454711168720557)
              ·
                refine ⟨7601902931045516688270209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20271741149454711168720557 7601902931045516688270209)
                ·
                  refine ⟨5701427198284137516202657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601902931045516688270209 5701427198284137516202657)
                  ·
                    refine ⟨4276070398713103137151993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701427198284137516202657 4276070398713103137151993)
                    ·
                      refine ⟨3207052799034827352863995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276070398713103137151993 3207052799034827352863995)
                      ·
                        rfl

theorem cell23_6245713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_6245713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245713 prefixEnd_6245713 := by exact prefixLift 6245713
  have htrace : WordTrace (prefixWord ++ tailWord_6245713) baseStart_6245713 baseEnd_6245713 := by
    simpa [prefixWord, tailWord_6245713, baseEnd_6245713] using wordTrace_append hprefix tailTrace_6245713
  have hstable : (prefixWord ++ tailWord_6245713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245713).length < 2 ^ (prefixWord ++ tailWord_6245713).sum := by decide
  have hdescent : baseEnd_6245713 < baseStart_6245713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245739 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 7, 2]
def baseStart_6245739 : Nat := 118140960795 + 6245739 * 2 ^ 59
def prefixEnd_6245739 : Nat := 4983230072969 + 3 ^ 40 * 6245739 * 2
def baseEnd_6245739 : Nat := 3207066149531844251138875

theorem tailTrace_6245739 : CollatzResearch.WordTrace tailWord_6245739 prefixEnd_6245739 3207066149531844251138875 := by
  unfold tailWord_6245739
  simp only [CollatzResearch.WordTrace]
  refine ⟨227800815919761765142996271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151867210613174510095330847 227800815919761765142996271)
  ·
    refine ⟨341701223879642647714494407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227800815919761765142996271 341701223879642647714494407)
    ·
      refine ⟨512551835819463971571741611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341701223879642647714494407 512551835819463971571741611)
      ·
        refine ⟨768827753729195957357612417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512551835819463971571741611 768827753729195957357612417)
        ·
          refine ⟨576620815296896968018209313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768827753729195957357612417 576620815296896968018209313)
          ·
            refine ⟨432465611472672726013656985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576620815296896968018209313 432465611472672726013656985)
            ·
              refine ⟨324349208604504544510242739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432465611472672726013656985 324349208604504544510242739)
              ·
                refine ⟨486523812906756816765364109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324349208604504544510242739 486523812906756816765364109)
                ·
                  refine ⟨182446429840033806287011541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486523812906756816765364109 182446429840033806287011541)
                  ·
                    refine ⟨4276088199375792334851833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182446429840033806287011541 4276088199375792334851833)
                    ·
                      refine ⟨3207066149531844251138875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276088199375792334851833 3207066149531844251138875)
                      ·
                        rfl

theorem cell23_6245739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7, 2].length) (baseStart_6245739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245739 prefixEnd_6245739 := by exact prefixLift 6245739
  have htrace : WordTrace (prefixWord ++ tailWord_6245739) baseStart_6245739 baseEnd_6245739 := by
    simpa [prefixWord, tailWord_6245739, baseEnd_6245739] using wordTrace_append hprefix tailTrace_6245739
  have hstable : (prefixWord ++ tailWord_6245739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245739).length < 2 ^ (prefixWord ++ tailWord_6245739).sum := by decide
  have hdescent : baseEnd_6245739 < baseStart_6245739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245786 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6245786 : Nat := 118140960795 + 6245786 * 2 ^ 59
def prefixEnd_6245786 : Nat := 4983230072969 + 3 ^ 40 * 6245786 * 2
def baseEnd_6245786 : Nat := 3207090283122605567251159

theorem tailTrace_6245786 : CollatzResearch.WordTrace tailWord_6245786 prefixEnd_6245786 3207090283122605567251159 := by
  unfold tailWord_6245786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56950632537647873042489303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151868353433727661446638141 56950632537647873042489303)
  ·
    refine ⟨85425948806471809563733955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56950632537647873042489303 85425948806471809563733955)
    ·
      refine ⟨128138923209707714345600933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85425948806471809563733955 128138923209707714345600933)
      ·
        refine ⟨24026048101820196439800175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128138923209707714345600933 24026048101820196439800175)
        ·
          refine ⟨36039072152730294659700263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24026048101820196439800175 36039072152730294659700263)
          ·
            refine ⟨54058608229095441989550395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039072152730294659700263 54058608229095441989550395)
            ·
              refine ⟨81087912343643162984325593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54058608229095441989550395 81087912343643162984325593)
              ·
                refine ⟨60815934257732372238244195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81087912343643162984325593 60815934257732372238244195)
                ·
                  refine ⟨91223901386598558357366293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60815934257732372238244195 91223901386598558357366293)
                  ·
                    refine ⟨4276120377496807423001545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91223901386598558357366293 4276120377496807423001545)
                    ·
                      refine ⟨3207090283122605567251159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276120377496807423001545 3207090283122605567251159)
                      ·
                        rfl

theorem cell23_6245786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6245786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245786 prefixEnd_6245786 := by exact prefixLift 6245786
  have htrace : WordTrace (prefixWord ++ tailWord_6245786) baseStart_6245786 baseEnd_6245786 := by
    simpa [prefixWord, tailWord_6245786, baseEnd_6245786] using wordTrace_append hprefix tailTrace_6245786
  have hstable : (prefixWord ++ tailWord_6245786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245786).length < 2 ^ (prefixWord ++ tailWord_6245786).sum := by decide
  have hdescent : baseEnd_6245786 < baseStart_6245786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245799 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6245799 : Nat := 118140960795 + 6245799 * 2 ^ 59
def prefixEnd_6245799 : Nat := 4983230072969 + 3 ^ 40 * 6245799 * 2
def baseEnd_6245799 : Nat := 3207096958371114016388599

theorem tailTrace_6245799 : CollatzResearch.WordTrace tailWord_6245799 prefixEnd_6245799 3207096958371114016388599 := by
  unfold tailWord_6245799
  simp only [CollatzResearch.WordTrace]
  refine ⟨227803004299544395390180451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151868669533029596926786967 227803004299544395390180451)
  ·
    refine ⟨341704506449316593085270677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227803004299544395390180451 341704506449316593085270677)
    ·
      refine ⟨16017398739811715300872063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 341704506449316593085270677 16017398739811715300872063)
      ·
        refine ⟨24026098109717572951308095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16017398739811715300872063 24026098109717572951308095)
        ·
          refine ⟨36039147164576359426962143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24026098109717572951308095 36039147164576359426962143)
          ·
            refine ⟨54058720746864539140443215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039147164576359426962143 54058720746864539140443215)
            ·
              refine ⟨81088081120296808710664823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54058720746864539140443215 81088081120296808710664823)
              ·
                refine ⟨121632121680445213065997235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81088081120296808710664823 121632121680445213065997235)
                ·
                  refine ⟨182448182520667819598995853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121632121680445213065997235 182448182520667819598995853)
                  ·
                    refine ⟨68418068445250432349623445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182448182520667819598995853 68418068445250432349623445)
                    ·
                      refine ⟨3207096958371114016388599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68418068445250432349623445 3207096958371114016388599)
                      ·
                        rfl

theorem cell23_6245799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6245799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245799 prefixEnd_6245799 := by exact prefixLift 6245799
  have htrace : WordTrace (prefixWord ++ tailWord_6245799) baseStart_6245799 baseEnd_6245799 := by
    simpa [prefixWord, tailWord_6245799, baseEnd_6245799] using wordTrace_append hprefix tailTrace_6245799
  have hstable : (prefixWord ++ tailWord_6245799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245799).length < 2 ^ (prefixWord ++ tailWord_6245799).sum := by decide
  have hdescent : baseEnd_6245799 < baseStart_6245799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245809 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 8]
def baseStart_6245809 : Nat := 118140960795 + 6245809 * 2 ^ 59
def prefixEnd_6245809 : Nat := 4983230072969 + 3 ^ 40 * 6245809 * 2
def baseEnd_6245809 : Nat := 356344677019739886362617

theorem tailTrace_6245809 : CollatzResearch.WordTrace tailWord_6245809 prefixEnd_6245809 356344677019739886362617 := by
  unfold tailWord_6245809
  simp only [CollatzResearch.WordTrace]
  refine ⟨227803369029508167098044481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151868912686338778065362987 227803369029508167098044481)
  ·
    refine ⟨170852526772131125323533361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227803369029508167098044481 170852526772131125323533361)
    ·
      refine ⟨128139395079098343992650021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170852526772131125323533361 128139395079098343992650021)
      ·
        refine ⟨24026136577330939498621879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128139395079098343992650021 24026136577330939498621879)
        ·
          refine ⟨36039204865996409247932819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24026136577330939498621879 36039204865996409247932819)
          ·
            refine ⟨54058807298994613871899229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039204865996409247932819 54058807298994613871899229)
            ·
              refine ⟨20272052737122980201962211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54058807298994613871899229 20272052737122980201962211)
              ·
                refine ⟨30408079105684470302943317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20272052737122980201962211 30408079105684470302943317)
                ·
                  refine ⟨356344677019739886362617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30408079105684470302943317 356344677019739886362617)
                  ·
                    rfl

theorem cell23_6245809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_6245809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245809 prefixEnd_6245809 := by exact prefixLift 6245809
  have htrace : WordTrace (prefixWord ++ tailWord_6245809) baseStart_6245809 baseEnd_6245809 := by
    simpa [prefixWord, tailWord_6245809, baseEnd_6245809] using wordTrace_append hprefix tailTrace_6245809
  have hstable : (prefixWord ++ tailWord_6245809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245809).length < 2 ^ (prefixWord ++ tailWord_6245809).sum := by decide
  have hdescent : baseEnd_6245809 < baseStart_6245809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245813 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_6245813 : Nat := 118140960795 + 6245813 * 2 ^ 59
def prefixEnd_6245813 : Nat := 4983230072969 + 3 ^ 40 * 6245813 * 2
def baseEnd_6245813 : Nat := 1069034715700092320537845

theorem tailTrace_6245813 : CollatzResearch.WordTrace tailWord_6245813 prefixEnd_6245813 1069034715700092320537845 := by
  unfold tailWord_6245813
  simp only [CollatzResearch.WordTrace]
  refine ⟨227803514921493675781190093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151869009947662450520793395 227803514921493675781190093)
  ·
    refine ⟨85426318095560128417946285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227803514921493675781190093 85426318095560128417946285)
    ·
      refine ⟨32034869285835048156729857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85426318095560128417946285 32034869285835048156729857)
      ·
        refine ⟨24026151964376286117547393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32034869285835048156729857 24026151964376286117547393)
        ·
          refine ⟨18019613973282214588160545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24026151964376286117547393 18019613973282214588160545)
          ·
            refine ⟨13514710479961660941120409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18019613973282214588160545 13514710479961660941120409)
            ·
              refine ⟨10136032859971245705840307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13514710479961660941120409 10136032859971245705840307)
              ·
                refine ⟨15204049289956868558760461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136032859971245705840307 15204049289956868558760461)
                ·
                  refine ⟨5701518483733825709535173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15204049289956868558760461 5701518483733825709535173)
                  ·
                    refine ⟨1069034715700092320537845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701518483733825709535173 1069034715700092320537845)
                    ·
                      rfl

theorem cell23_6245813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_6245813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245813 prefixEnd_6245813 := by exact prefixLift 6245813
  have htrace : WordTrace (prefixWord ++ tailWord_6245813) baseStart_6245813 baseEnd_6245813 := by
    simpa [prefixWord, tailWord_6245813, baseEnd_6245813] using wordTrace_append hprefix tailTrace_6245813
  have hstable : (prefixWord ++ tailWord_6245813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245813).length < 2 ^ (prefixWord ++ tailWord_6245813).sum := by decide
  have hdescent : baseEnd_6245813 < baseStart_6245813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245839 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 3, 5]
def baseStart_6245839 : Nat := 118140960795 + 6245839 * 2 ^ 59
def prefixEnd_6245839 : Nat := 4983230072969 + 3 ^ 40 * 6245839 * 2
def baseEnd_6245839 : Nat := 1069039165865764619962805

theorem tailTrace_6245839 : CollatzResearch.WordTrace tailWord_6245839 prefixEnd_6245839 1069039165865764619962805 := by
  unfold tailWord_6245839
  simp only [CollatzResearch.WordTrace]
  refine ⟨227804463219399482221636571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151869642146266321481091047 227804463219399482221636571)
  ·
    refine ⟨341706694829099223332454857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227804463219399482221636571 341706694829099223332454857)
    ·
      refine ⟨256280021121824417499341143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341706694829099223332454857 256280021121824417499341143)
      ·
        refine ⟨384420031682736626249011715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256280021121824417499341143 384420031682736626249011715)
        ·
          refine ⟨576630047524104939373517573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384420031682736626249011715 576630047524104939373517573)
          ·
            refine ⟨108118133910769676132534545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576630047524104939373517573 108118133910769676132534545)
            ·
              refine ⟨81088600433077257099400909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108118133910769676132534545 81088600433077257099400909)
              ·
                refine ⟨30408225162403971412275341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81088600433077257099400909 30408225162403971412275341)
                ·
                  refine ⟨11403084435901489279603253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30408225162403971412275341 11403084435901489279603253)
                  ·
                    refine ⟨1069039165865764619962805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11403084435901489279603253 1069039165865764619962805)
                    ·
                      rfl

theorem cell23_6245839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_6245839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245839 prefixEnd_6245839 := by exact prefixLift 6245839
  have htrace : WordTrace (prefixWord ++ tailWord_6245839) baseStart_6245839 baseEnd_6245839 := by
    simpa [prefixWord, tailWord_6245839, baseEnd_6245839] using wordTrace_append hprefix tailTrace_6245839
  have hstable : (prefixWord ++ tailWord_6245839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245839).length < 2 ^ (prefixWord ++ tailWord_6245839).sum := by decide
  have hdescent : baseEnd_6245839 < baseStart_6245839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245863 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6245863 : Nat := 118140960795 + 6245863 * 2 ^ 59
def prefixEnd_6245863 : Nat := 4983230072969 + 3 ^ 40 * 6245863 * 2
def baseEnd_6245863 : Nat := 3207129821133001765988305

theorem tailTrace_6245863 : CollatzResearch.WordTrace tailWord_6245863 prefixEnd_6245863 3207129821133001765988305 := by
  unfold tailWord_6245863
  simp only [CollatzResearch.WordTrace]
  refine ⟨227805338571312534320510243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151870225714208356213673495 227805338571312534320510243)
  ·
    refine ⟨341708007856968801480765365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227805338571312534320510243 341708007856968801480765365)
    ·
      refine ⟨32035125736590825138821753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341708007856968801480765365 32035125736590825138821753)
      ·
        refine ⟨24026344302443118854116315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32035125736590825138821753 24026344302443118854116315)
        ·
          refine ⟨36039516453664678281174473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24026344302443118854116315 36039516453664678281174473)
          ·
            refine ⟨27029637340248508710880855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36039516453664678281174473 27029637340248508710880855)
            ·
              refine ⟨40544456010372763066321283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27029637340248508710880855 40544456010372763066321283)
              ·
                refine ⟨60816684015559144599481925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40544456010372763066321283 60816684015559144599481925)
                ·
                  refine ⟨11403128252917339612402861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60816684015559144599481925 11403128252917339612402861)
                  ·
                    refine ⟨4276173094844002354651073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11403128252917339612402861 4276173094844002354651073)
                    ·
                      refine ⟨3207129821133001765988305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276173094844002354651073 3207129821133001765988305)
                      ·
                        rfl

theorem cell23_6245863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6245863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245863 prefixEnd_6245863 := by exact prefixLift 6245863
  have htrace : WordTrace (prefixWord ++ tailWord_6245863) baseStart_6245863 baseEnd_6245863 := by
    simpa [prefixWord, tailWord_6245863, baseEnd_6245863] using wordTrace_append hprefix tailTrace_6245863
  have hstable : (prefixWord ++ tailWord_6245863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245863).length < 2 ^ (prefixWord ++ tailWord_6245863).sum := by decide
  have hdescent : baseEnd_6245863 < baseStart_6245863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245879 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_6245879 : Nat := 118140960795 + 6245879 * 2 ^ 59
def prefixEnd_6245879 : Nat := 4983230072969 + 3 ^ 40 * 6245879 * 2
def baseEnd_6245879 : Nat := 3207138036823473703388231

theorem tailTrace_6245879 : CollatzResearch.WordTrace tailWord_6245879 prefixEnd_6245879 3207138036823473703388231 := by
  unfold tailWord_6245879
  simp only [CollatzResearch.WordTrace]
  refine ⟨227805922139254569053092691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151870614759503046035395127 227805922139254569053092691)
  ·
    refine ⟨341708883208881853579639037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227805922139254569053092691 341708883208881853579639037)
    ·
      refine ⟨128140831203330695092364639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341708883208881853579639037 128140831203330695092364639)
      ·
        refine ⟨192211246804996042638546959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128140831203330695092364639 192211246804996042638546959)
        ·
          refine ⟨288316870207494063957820439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192211246804996042638546959 288316870207494063957820439)
          ·
            refine ⟨432475305311241095936730659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288316870207494063957820439 432475305311241095936730659)
            ·
              refine ⟨648712957966861643905095989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432475305311241095936730659 648712957966861643905095989)
              ·
                refine ⟨60816839809393279116102749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648712957966861643905095989 60816839809393279116102749)
                ·
                  refine ⟨22806314928522479668538531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60816839809393279116102749 22806314928522479668538531)
                  ·
                    refine ⟨34209472392783719502807797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22806314928522479668538531 34209472392783719502807797)
                    ·
                      refine ⟨3207138036823473703388231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34209472392783719502807797 3207138036823473703388231)
                      ·
                        rfl

theorem cell23_6245879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_6245879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245879 prefixEnd_6245879 := by exact prefixLift 6245879
  have htrace : WordTrace (prefixWord ++ tailWord_6245879) baseStart_6245879 baseEnd_6245879 := by
    simpa [prefixWord, tailWord_6245879, baseEnd_6245879] using wordTrace_append hprefix tailTrace_6245879
  have hstable : (prefixWord ++ tailWord_6245879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245879).length < 2 ^ (prefixWord ++ tailWord_6245879).sum := by decide
  have hdescent : baseEnd_6245879 < baseStart_6245879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245890 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6245890 : Nat := 118140960795 + 6245890 * 2 ^ 59
def prefixEnd_6245890 : Nat := 4983230072969 + 3 ^ 40 * 6245890 * 2
def baseEnd_6245890 : Nat := 1069047895036891053450227

theorem tailTrace_6245890 : CollatzResearch.WordTrace tailWord_6245890 prefixEnd_6245890 1069047895036891053450227 := by
  unfold tailWord_6245890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951580835553679482935781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151870882228143145287828749 56951580835553679482935781)
  ·
    refine ⟨10678421406666314903050459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56951580835553679482935781 10678421406666314903050459)
    ·
      refine ⟨16017632109999472354575689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10678421406666314903050459 16017632109999472354575689)
      ·
        refine ⟨12013224082499604265931767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16017632109999472354575689 12013224082499604265931767)
        ·
          refine ⟨18019836123749406398897651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12013224082499604265931767 18019836123749406398897651)
          ·
            refine ⟨27029754185624109598346477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18019836123749406398897651 27029754185624109598346477)
            ·
              refine ⟨10136157819609041099379929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27029754185624109598346477 10136157819609041099379929)
              ·
                refine ⟨7602118364706780824534947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10136157819609041099379929 7602118364706780824534947)
                ·
                  refine ⟨11403177547060171236802421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602118364706780824534947 11403177547060171236802421)
                  ·
                    refine ⟨1069047895036891053450227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11403177547060171236802421 1069047895036891053450227)
                    ·
                      rfl

theorem cell23_6245890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6245890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245890 prefixEnd_6245890 := by exact prefixLift 6245890
  have htrace : WordTrace (prefixWord ++ tailWord_6245890) baseStart_6245890 baseEnd_6245890 := by
    simpa [prefixWord, tailWord_6245890, baseEnd_6245890] using wordTrace_append hprefix tailTrace_6245890
  have hstable : (prefixWord ++ tailWord_6245890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245890).length < 2 ^ (prefixWord ++ tailWord_6245890).sum := by decide
  have hdescent : baseEnd_6245890 < baseStart_6245890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245893 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_6245893 : Nat := 118140960795 + 6245893 * 2 ^ 59
def prefixEnd_6245893 : Nat := 4983230072969 + 3 ^ 40 * 6245893 * 2
def baseEnd_6245893 : Nat := 3207145225552636648613167

theorem tailTrace_6245893 : CollatzResearch.WordTrace tailWord_6245893 prefixEnd_6245893 3207145225552636648613167 := by
  unfold tailWord_6245893
  simp only [CollatzResearch.WordTrace]
  refine ⟨227806432761203849444102333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151870955174135899629401555 227806432761203849444102333)
  ·
    refine ⟨85427412285451443541538375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227806432761203849444102333 85427412285451443541538375)
    ·
      refine ⟨128141118428177165312307563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85427412285451443541538375 128141118428177165312307563)
      ·
        refine ⟨192211677642265747968461345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128141118428177165312307563 192211677642265747968461345)
        ·
          refine ⟨144158758231699310976346009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192211677642265747968461345 144158758231699310976346009)
          ·
            refine ⟨108119068673774483232259507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144158758231699310976346009 108119068673774483232259507)
            ·
              refine ⟨162178603010661724848389261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108119068673774483232259507 162178603010661724848389261)
              ·
                refine ⟨60816976128998146818145973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162178603010661724848389261 60816976128998146818145973)
                ·
                  refine ⟨5701591512093576264201185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60816976128998146818145973 5701591512093576264201185)
                  ·
                    refine ⟨4276193634070182198150889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5701591512093576264201185 4276193634070182198150889)
                    ·
                      refine ⟨3207145225552636648613167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276193634070182198150889 3207145225552636648613167)
                      ·
                        rfl

theorem cell23_6245893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_6245893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245893 prefixEnd_6245893 := by exact prefixLift 6245893
  have htrace : WordTrace (prefixWord ++ tailWord_6245893) baseStart_6245893 baseEnd_6245893 := by
    simpa [prefixWord, tailWord_6245893, baseEnd_6245893] using wordTrace_append hprefix tailTrace_6245893
  have hstable : (prefixWord ++ tailWord_6245893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245893).length < 2 ^ (prefixWord ++ tailWord_6245893).sum := by decide
  have hdescent : baseEnd_6245893 < baseStart_6245893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245920 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_6245920 : Nat := 118140960795 + 6245920 * 2 ^ 59
def prefixEnd_6245920 : Nat := 4983230072969 + 3 ^ 40 * 6245920 * 2
def baseEnd_6245920 : Nat := 1069053029843436014325181

theorem tailTrace_6245920 : CollatzResearch.WordTrace tailWord_6245920 prefixEnd_6245920 1069053029843436014325181 := by
  unfold tailWord_6245920
  simp only [CollatzResearch.WordTrace]
  refine ⟨113903708766053016527667607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151871611688070688703556809 113903708766053016527667607)
  ·
    refine ⟨170855563149079524791501411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113903708766053016527667607 170855563149079524791501411)
    ·
      refine ⟨256283344723619287187252117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170855563149079524791501411 256283344723619287187252117)
      ·
        refine ⟨12013281783919654086902443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256283344723619287187252117 12013281783919654086902443)
        ·
          refine ⟨18019922675879481130353665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12013281783919654086902443 18019922675879481130353665)
          ·
            refine ⟨13514942006909610847765249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18019922675879481130353665 13514942006909610847765249)
            ·
              refine ⟨10136206505182208135823937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13514942006909610847765249 10136206505182208135823937)
              ·
                refine ⟨7602154878886656101867953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10136206505182208135823937 7602154878886656101867953)
                ·
                  refine ⟨5701616159164992076400965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7602154878886656101867953 5701616159164992076400965)
                  ·
                    refine ⟨1069053029843436014325181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701616159164992076400965 1069053029843436014325181)
                    ·
                      rfl

theorem cell23_6245920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_6245920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245920 prefixEnd_6245920 := by exact prefixLift 6245920
  have htrace : WordTrace (prefixWord ++ tailWord_6245920) baseStart_6245920 baseEnd_6245920 := by
    simpa [prefixWord, tailWord_6245920, baseEnd_6245920] using wordTrace_append hprefix tailTrace_6245920
  have hstable : (prefixWord ++ tailWord_6245920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245920).length < 2 ^ (prefixWord ++ tailWord_6245920).sum := by decide
  have hdescent : baseEnd_6245920 < baseStart_6245920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6245943 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_6245943 : Nat := 118140960795 + 6245943 * 2 ^ 59
def prefixEnd_6245943 : Nat := 4983230072969 + 3 ^ 40 * 6245943 * 2
def baseEnd_6245943 : Nat := 3207170899585361452987937

theorem tailTrace_6245943 : CollatzResearch.WordTrace tailWord_6245943 prefixEnd_6245943 3207170899585361452987937 := by
  unfold tailWord_6245943
  simp only [CollatzResearch.WordTrace]
  refine ⟨227808256411022707983422483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151872170940681805322281655 227808256411022707983422483)
  ·
    refine ⟨341712384616534061975133725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227808256411022707983422483 341712384616534061975133725)
    ·
      refine ⟨128142144231200273240675147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341712384616534061975133725 128142144231200273240675147)
      ·
        refine ⟨192213216346800409861012721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128142144231200273240675147 192213216346800409861012721)
        ·
          refine ⟨144159912260100307395759541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192213216346800409861012721 144159912260100307395759541)
          ·
            refine ⟨13514991774384403818352457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144159912260100307395759541 13514991774384403818352457)
            ·
              refine ⟨10136243830788302863764343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13514991774384403818352457 10136243830788302863764343)
              ·
                refine ⟨15204365746182454295646515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136243830788302863764343 15204365746182454295646515)
                ·
                  refine ⟨22806548619273681443469773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15204365746182454295646515 22806548619273681443469773)
                  ·
                    refine ⟨8552455732227630541301165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22806548619273681443469773 8552455732227630541301165)
                    ·
                      refine ⟨3207170899585361452987937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8552455732227630541301165 3207170899585361452987937)
                      ·
                        rfl

theorem cell23_6245943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_6245943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6245943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6245943 prefixEnd_6245943 := by exact prefixLift 6245943
  have htrace : WordTrace (prefixWord ++ tailWord_6245943) baseStart_6245943 baseEnd_6245943 := by
    simpa [prefixWord, tailWord_6245943, baseEnd_6245943] using wordTrace_append hprefix tailTrace_6245943
  have hstable : (prefixWord ++ tailWord_6245943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6245943).length < 2 ^ (prefixWord ++ tailWord_6245943).sum := by decide
  have hdescent : baseEnd_6245943 < baseStart_6245943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6245943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6246000 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2]
def baseStart_6246000 : Nat := 118140960795 + 6246000 * 2 ^ 59
def prefixEnd_6246000 : Nat := 4983230072969 + 3 ^ 40 * 6246000 * 2
def baseEnd_6246000 : Nat := 3207200167982667729975175

theorem tailTrace_6246000 : CollatzResearch.WordTrace tailWord_6246000 prefixEnd_6246000 3207200167982667729975175 := by
  unfold tailWord_6246000
  simp only [CollatzResearch.WordTrace]
  refine ⟨113905167685908103359123727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151873556914544137812164969 113905167685908103359123727)
  ·
    refine ⟨170857751528862155038685591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113905167685908103359123727 170857751528862155038685591)
    ·
      refine ⟨256286627293293232558028387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170857751528862155038685591 256286627293293232558028387)
      ·
        refine ⟨384429940939939848837042581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256286627293293232558028387 384429940939939848837042581)
        ·
          refine ⟨18020153481559680414236371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 384429940939939848837042581 18020153481559680414236371)
          ·
            refine ⟨27030230222339520621354557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18020153481559680414236371 27030230222339520621354557)
            ·
              refine ⟨10136336333377320233007959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27030230222339520621354557 10136336333377320233007959)
              ·
                refine ⟨15204504500065980349511939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136336333377320233007959 15204504500065980349511939)
                ·
                  refine ⟨22806756750098970524267909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15204504500065980349511939 22806756750098970524267909)
                  ·
                    refine ⟨4276266890643556973300233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22806756750098970524267909 4276266890643556973300233)
                    ·
                      refine ⟨3207200167982667729975175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4276266890643556973300233 3207200167982667729975175)
                      ·
                        rfl

theorem cell23_6246000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2].length) (baseStart_6246000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6246000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6246000 prefixEnd_6246000 := by exact prefixLift 6246000
  have htrace : WordTrace (prefixWord ++ tailWord_6246000) baseStart_6246000 baseEnd_6246000 := by
    simpa [prefixWord, tailWord_6246000, baseEnd_6246000] using wordTrace_append hprefix tailTrace_6246000
  have hstable : (prefixWord ++ tailWord_6246000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6246000).length < 2 ^ (prefixWord ++ tailWord_6246000).sum := by decide
  have hdescent : baseEnd_6246000 < baseStart_6246000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6246000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
