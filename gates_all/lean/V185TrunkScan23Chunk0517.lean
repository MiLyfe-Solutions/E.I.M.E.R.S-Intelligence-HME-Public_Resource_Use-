import V185TrunkScan23Chunk0516

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3057334 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3057334 : Nat := 118140960795 + 3057334 * 2 ^ 59
def prefixEnd_3057334 : Nat := 4983230072969 + 3 ^ 40 * 3057334 * 2
def baseEnd_3057334 : Nat := 1569881863333246400364583

theorem tailTrace_3057334 : CollatzResearch.WordTrace tailWord_3057334 prefixEnd_3057334 1569881863333246400364583 := by
  unfold tailWord_3057334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6969383244113033995108691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74340087937205695947826037 6969383244113033995108691)
  ·
    refine ⟨10454074866169550992663037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6969383244113033995108691 10454074866169550992663037)
    ·
      refine ⟨3920278074813581622248639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10454074866169550992663037 3920278074813581622248639)
      ·
        refine ⟨5880417112220372433372959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920278074813581622248639 5880417112220372433372959)
        ·
          refine ⟨8820625668330558650059439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5880417112220372433372959 8820625668330558650059439)
          ·
            refine ⟨13230938502495837975089159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820625668330558650059439 13230938502495837975089159)
            ·
              refine ⟨19846407753743756962633739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230938502495837975089159 19846407753743756962633739)
              ·
                refine ⟨29769611630615635443950609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19846407753743756962633739 29769611630615635443950609)
                ·
                  refine ⟨22327208722961726582962957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29769611630615635443950609 22327208722961726582962957)
                  ·
                    refine ⟨8372703271110647468611109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22327208722961726582962957 8372703271110647468611109)
                    ·
                      refine ⟨1569881863333246400364583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8372703271110647468611109 1569881863333246400364583)
                      ·
                        rfl

theorem cell23_3057334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3057334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057334 prefixEnd_3057334 := by exact prefixLift 3057334
  have htrace : WordTrace (prefixWord ++ tailWord_3057334) baseStart_3057334 baseEnd_3057334 := by
    simpa [prefixWord, tailWord_3057334, baseEnd_3057334] using wordTrace_append hprefix tailTrace_3057334
  have hstable : (prefixWord ++ tailWord_3057334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057334).length < 2 ^ (prefixWord ++ tailWord_3057334).sum := by decide
  have hdescent : baseEnd_3057334 < baseStart_3057334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057372 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3057372 : Nat := 118140960795 + 3057372 * 2 ^ 59
def prefixEnd_3057372 : Nat := 4983230072969 + 3 ^ 40 * 3057372 * 2
def baseEnd_3057372 : Nat := 1569901375598117251689409

theorem tailTrace_3057372 : CollatzResearch.WordTrace tailWord_3057372 prefixEnd_3057372 1569901375598117251689409 := by
  unfold tailWord_3057372
  simp only [CollatzResearch.WordTrace]
  refine ⟨55755758939835438205811185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74341011919780584274414913 55755758939835438205811185)
  ·
    refine ⟨41816819204876578654358389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55755758939835438205811185 41816819204876578654358389)
    ·
      refine ⟨3920326800457179248846099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41816819204876578654358389 3920326800457179248846099)
      ·
        refine ⟨5880490200685768873269149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920326800457179248846099 5880490200685768873269149)
        ·
          refine ⟨2205183825257163327475931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5880490200685768873269149 2205183825257163327475931)
          ·
            refine ⟨3307775737885744991213897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205183825257163327475931 3307775737885744991213897)
            ·
              refine ⟨2480831803414308743410423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307775737885744991213897 2480831803414308743410423)
              ·
                refine ⟨3721247705121463115115635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480831803414308743410423 3721247705121463115115635)
                ·
                  refine ⟨5581871557682194672673453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721247705121463115115635 5581871557682194672673453)
                  ·
                    refine ⟨2093201834130823002252545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5581871557682194672673453 2093201834130823002252545)
                    ·
                      refine ⟨1569901375598117251689409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093201834130823002252545 1569901375598117251689409)
                      ·
                        rfl

theorem cell23_3057372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3057372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057372 prefixEnd_3057372 := by exact prefixLift 3057372
  have htrace : WordTrace (prefixWord ++ tailWord_3057372) baseStart_3057372 baseEnd_3057372 := by
    simpa [prefixWord, tailWord_3057372, baseEnd_3057372] using wordTrace_append hprefix tailTrace_3057372
  have hstable : (prefixWord ++ tailWord_3057372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057372).length < 2 ^ (prefixWord ++ tailWord_3057372).sum := by decide
  have hdescent : baseEnd_3057372 < baseStart_3057372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057438 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3057438 : Nat := 118140960795 + 3057438 * 2 ^ 59
def prefixEnd_3057438 : Nat := 4983230072969 + 3 ^ 40 * 3057438 * 2
def baseEnd_3057438 : Nat := 523311755107104664488035

theorem tailTrace_3057438 : CollatzResearch.WordTrace tailWord_3057438 prefixEnd_3057438 523311755107104664488035 := by
  unfold tailWord_3057438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939240637178971210440621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74342616731621179789016645 13939240637178971210440621)
  ·
    refine ⟨5227215238942114203915233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13939240637178971210440621 5227215238942114203915233)
    ·
      refine ⟨3920411429206585652936425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5227215238942114203915233 3920411429206585652936425)
      ·
        refine ⟨2940308571904939239702319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3920411429206585652936425 2940308571904939239702319)
        ·
          refine ⟨4410462857857408859553479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940308571904939239702319 4410462857857408859553479)
          ·
            refine ⟨6615694286786113289330219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410462857857408859553479 6615694286786113289330219)
            ·
              refine ⟨9923541430179169933995329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615694286786113289330219 9923541430179169933995329)
              ·
                refine ⟨7442656072634377450496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9923541430179169933995329 7442656072634377450496497)
                ·
                  refine ⟨5581992054475783087872373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442656072634377450496497 5581992054475783087872373)
                  ·
                    refine ⟨523311755107104664488035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5581992054475783087872373 523311755107104664488035)
                    ·
                      rfl

theorem cell23_3057438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3057438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057438 prefixEnd_3057438 := by exact prefixLift 3057438
  have htrace : WordTrace (prefixWord ++ tailWord_3057438) baseStart_3057438 baseEnd_3057438 := by
    simpa [prefixWord, tailWord_3057438, baseEnd_3057438] using wordTrace_append hprefix tailTrace_3057438
  have hstable : (prefixWord ++ tailWord_3057438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057438).length < 2 ^ (prefixWord ++ tailWord_3057438).sum := by decide
  have hdescent : baseEnd_3057438 < baseStart_3057438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057444 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3057444 : Nat := 118140960795 + 3057444 * 2 ^ 59
def prefixEnd_3057444 : Nat := 4983230072969 + 3 ^ 40 * 3057444 * 2
def baseEnd_3057444 : Nat := 1569938346205240969989077

theorem tailTrace_3057444 : CollatzResearch.WordTrace tailWord_3057444 prefixEnd_3057444 1569938346205240969989077 := by
  unfold tailWord_3057444
  simp only [CollatzResearch.WordTrace]
  refine ⟨55757071967705016354121693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74342762623606688472162257 55757071967705016354121693)
  ·
    refine ⟨20908901987889381132795635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55757071967705016354121693 20908901987889381132795635)
    ·
      refine ⟨31363352981834071699193453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20908901987889381132795635 31363352981834071699193453)
      ·
        refine ⟨11761257368187776887197545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31363352981834071699193453 11761257368187776887197545)
        ·
          refine ⟨8820943026140832665398159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11761257368187776887197545 8820943026140832665398159)
          ·
            refine ⟨13231414539211248998097239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820943026140832665398159 13231414539211248998097239)
            ·
              refine ⟨19847121808816873497145859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231414539211248998097239 19847121808816873497145859)
              ·
                refine ⟨29770682713225310245718789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19847121808816873497145859 29770682713225310245718789)
                ·
                  refine ⟨5582003008729745671072273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29770682713225310245718789 5582003008729745671072273)
                  ·
                    refine ⟨4186502256547309253304205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582003008729745671072273 4186502256547309253304205)
                    ·
                      refine ⟨1569938346205240969989077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186502256547309253304205 1569938346205240969989077)
                      ·
                        rfl

theorem cell23_3057444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3057444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057444 prefixEnd_3057444 := by exact prefixLift 3057444
  have htrace : WordTrace (prefixWord ++ tailWord_3057444) baseStart_3057444 baseEnd_3057444 := by
    simpa [prefixWord, tailWord_3057444, baseEnd_3057444] using wordTrace_append hprefix tailTrace_3057444
  have hstable : (prefixWord ++ tailWord_3057444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057444).length < 2 ^ (prefixWord ++ tailWord_3057444).sum := by decide
  have hdescent : baseEnd_3057444 < baseStart_3057444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057464 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 6]
def baseStart_3057464 : Nat := 118140960795 + 3057464 * 2 ^ 59
def prefixEnd_3057464 : Nat := 4983230072969 + 3 ^ 40 * 3057464 * 2
def baseEnd_3057464 : Nat := 174438735090925654637665

theorem tailTrace_3057464 : CollatzResearch.WordTrace tailWord_3057464 prefixEnd_3057464 174438735090925654637665 := by
  unfold tailWord_3057464
  simp only [CollatzResearch.WordTrace]
  refine ⟨55757436697668788061985723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74343248930225050749314297 55757436697668788061985723)
  ·
    refine ⟨83636155046503182092978585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55757436697668788061985723 83636155046503182092978585)
    ·
      refine ⟨62727116284877386569733939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83636155046503182092978585 62727116284877386569733939)
      ·
        refine ⟨94090674427316079854600909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62727116284877386569733939 94090674427316079854600909)
        ·
          refine ⟨35284002910243529945475341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94090674427316079854600909 35284002910243529945475341)
          ·
            refine ⟨13231501091341323729553253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35284002910243529945475341 13231501091341323729553253)
            ·
              refine ⟨2480906454626498199291235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13231501091341323729553253 2480906454626498199291235)
              ·
                refine ⟨3721359681939747298936853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480906454626498199291235 3721359681939747298936853)
                ·
                  refine ⟨174438735090925654637665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3721359681939747298936853 174438735090925654637665)
                  ·
                    rfl

theorem cell23_3057464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_3057464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057464 prefixEnd_3057464 := by exact prefixLift 3057464
  have htrace : WordTrace (prefixWord ++ tailWord_3057464) baseStart_3057464 baseEnd_3057464 := by
    simpa [prefixWord, tailWord_3057464, baseEnd_3057464] using wordTrace_append hprefix tailTrace_3057464
  have hstable : (prefixWord ++ tailWord_3057464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057464).length < 2 ^ (prefixWord ++ tailWord_3057464).sum := by decide
  have hdescent : baseEnd_3057464 < baseStart_3057464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057477 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_3057477 : Nat := 118140960795 + 3057477 * 2 ^ 59
def prefixEnd_3057477 : Nat := 4983230072969 + 3 ^ 40 * 3057477 * 2
def baseEnd_3057477 : Nat := 523318430355613113625475

theorem tailTrace_3057477 : CollatzResearch.WordTrace tailWord_3057477 prefixEnd_3057477 523318430355613113625475 := by
  unfold tailWord_3057477
  simp only [CollatzResearch.WordTrace]
  refine ⟨111515347544290479344194685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74343565029526986229463123 111515347544290479344194685)
  ·
    refine ⟨41818255329108929754073007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111515347544290479344194685 41818255329108929754073007)
    ·
      refine ⟨62727382993663394631109511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41818255329108929754073007 62727382993663394631109511)
      ·
        refine ⟨94091074490495091946664267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62727382993663394631109511 94091074490495091946664267)
        ·
          refine ⟨141136611735742637919996401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94091074490495091946664267 141136611735742637919996401)
          ·
            refine ⟨105852458801806978439997301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141136611735742637919996401 105852458801806978439997301)
            ·
              refine ⟨9923668012669404228749747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105852458801806978439997301 9923668012669404228749747)
              ·
                refine ⟨14885502019004106343124621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9923668012669404228749747 14885502019004106343124621)
                ·
                  refine ⟨5582063257126539878671733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14885502019004106343124621 5582063257126539878671733)
                  ·
                    refine ⟨523318430355613113625475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5582063257126539878671733 523318430355613113625475)
                    ·
                      rfl

theorem cell23_3057477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_3057477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057477 prefixEnd_3057477 := by exact prefixLift 3057477
  have htrace : WordTrace (prefixWord ++ tailWord_3057477) baseStart_3057477 baseEnd_3057477 := by
    simpa [prefixWord, tailWord_3057477, baseEnd_3057477] using wordTrace_append hprefix tailTrace_3057477
  have hstable : (prefixWord ++ tailWord_3057477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057477).length < 2 ^ (prefixWord ++ tailWord_3057477).sum := by decide
  have hdescent : baseEnd_3057477 < baseStart_3057477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057478 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3057478 : Nat := 118140960795 + 3057478 * 2 ^ 59
def prefixEnd_3057478 : Nat := 4983230072969 + 3 ^ 40 * 3057478 * 2
def baseEnd_3057478 : Nat := 1569955804547493836963921

theorem tailTrace_3057478 : CollatzResearch.WordTrace tailWord_3057478 prefixEnd_3057478 1569955804547493836963921 := by
  unfold tailWord_3057478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484855750540214266093159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74343589344857904343320725 3484855750540214266093159)
  ·
    refine ⟨5227283625810321399139739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3484855750540214266093159 5227283625810321399139739)
    ·
      refine ⟨7840925438715482098709609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227283625810321399139739 7840925438715482098709609)
      ·
        refine ⟨5880694079036611574032207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7840925438715482098709609 5880694079036611574032207)
        ·
          refine ⟨8821041118554917361048311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5880694079036611574032207 8821041118554917361048311)
          ·
            refine ⟨13231561677832376041572467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8821041118554917361048311 13231561677832376041572467)
            ·
              refine ⟨19847342516748564062358701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231561677832376041572467 19847342516748564062358701)
              ·
                refine ⟨7442753443780711523384513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19847342516748564062358701 7442753443780711523384513)
                ·
                  refine ⟨5582065082835533642538385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442753443780711523384513 5582065082835533642538385)
                  ·
                    refine ⟨4186548812126650231903789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582065082835533642538385 4186548812126650231903789)
                    ·
                      refine ⟨1569955804547493836963921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186548812126650231903789 1569955804547493836963921)
                      ·
                        rfl

theorem cell23_3057478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3057478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057478 prefixEnd_3057478 := by exact prefixLift 3057478
  have htrace : WordTrace (prefixWord ++ tailWord_3057478) baseStart_3057478 baseEnd_3057478 := by
    simpa [prefixWord, tailWord_3057478, baseEnd_3057478] using wordTrace_append hprefix tailTrace_3057478
  have hstable : (prefixWord ++ tailWord_3057478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057478).length < 2 ^ (prefixWord ++ tailWord_3057478).sum := by decide
  have hdescent : baseEnd_3057478 < baseStart_3057478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057554 : List Nat := [3, 2, 3, 2, 1, 2, 10]
def baseStart_3057554 : Nat := 118140960795 + 3057554 * 2 ^ 59
def prefixEnd_3057554 : Nat := 4983230072969 + 3 ^ 40 * 3057554 * 2
def baseEnd_3057554 : Nat := 19382652210830068390291

theorem tailTrace_3057554 : CollatzResearch.WordTrace tailWord_3057554 prefixEnd_3057554 19382652210830068390291 := by
  unfold tailWord_3057554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879538991252880373686929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74345437310007680996498477 27879538991252880373686929)
  ·
    refine ⟨20909654243439660280265197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27879538991252880373686929 20909654243439660280265197)
    ·
      refine ⟨7841120341289872605099449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20909654243439660280265197 7841120341289872605099449)
      ·
        refine ⟨5880840255967404453824587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841120341289872605099449 5880840255967404453824587)
        ·
          refine ⟨8821260383951106680736881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5880840255967404453824587 8821260383951106680736881)
          ·
            refine ⟨6615945287963330010552661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8821260383951106680736881 6615945287963330010552661)
            ·
              refine ⟨19382652210830068390291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6615945287963330010552661 19382652210830068390291)
              ·
                rfl

theorem cell23_3057554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 10].length) (baseStart_3057554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057554 prefixEnd_3057554 := by exact prefixLift 3057554
  have htrace : WordTrace (prefixWord ++ tailWord_3057554) baseStart_3057554 baseEnd_3057554 := by
    simpa [prefixWord, tailWord_3057554, baseEnd_3057554] using wordTrace_append hprefix tailTrace_3057554
  have hstable : (prefixWord ++ tailWord_3057554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057554).length < 2 ^ (prefixWord ++ tailWord_3057554).sum := by decide
  have hdescent : baseEnd_3057554 < baseStart_3057554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057565 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_3057565 : Nat := 118140960795 + 3057565 * 2 ^ 59
def prefixEnd_3057565 : Nat := 4983230072969 + 3 ^ 40 * 3057565 * 2
def baseEnd_3057565 : Nat := 1570000477364434996576021

theorem tailTrace_3057565 : CollatzResearch.WordTrace tailWord_3057565 prefixEnd_3057565 1570000477364434996576021 := by
  unfold tailWord_3057565
  simp only [CollatzResearch.WordTrace]
  refine ⟨111518557167971670373398149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74345704778647780248932099 111518557167971670373398149)
  ·
    refine ⟨20909729468994688195012153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111518557167971670373398149 20909729468994688195012153)
    ·
      refine ⟨15682297101746016146259115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20909729468994688195012153 15682297101746016146259115)
      ·
        refine ⟨23523445652619024219388673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15682297101746016146259115 23523445652619024219388673)
        ·
          refine ⟨17642584239464268164541505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23523445652619024219388673 17642584239464268164541505)
          ·
            refine ⟨13231938179598201123406129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17642584239464268164541505 13231938179598201123406129)
            ·
              refine ⟨9923953634698650842554597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13231938179598201123406129 9923953634698650842554597)
              ·
                refine ⟨1860741306505997032978987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9923953634698650842554597 1860741306505997032978987)
                ·
                  refine ⟨2791111959758995549468481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860741306505997032978987 2791111959758995549468481)
                  ·
                    refine ⟨2093333969819246662101361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791111959758995549468481 2093333969819246662101361)
                    ·
                      refine ⟨1570000477364434996576021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093333969819246662101361 1570000477364434996576021)
                      ·
                        rfl

theorem cell23_3057565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_3057565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057565 prefixEnd_3057565 := by exact prefixLift 3057565
  have htrace : WordTrace (prefixWord ++ tailWord_3057565) baseStart_3057565 baseEnd_3057565 := by
    simpa [prefixWord, tailWord_3057565, baseEnd_3057565] using wordTrace_append hprefix tailTrace_3057565
  have hstable : (prefixWord ++ tailWord_3057565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057565).length < 2 ^ (prefixWord ++ tailWord_3057565).sum := by decide
  have hdescent : baseEnd_3057565 < baseStart_3057565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057582 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3057582 : Nat := 118140960795 + 3057582 * 2 ^ 59
def prefixEnd_3057582 : Nat := 4983230072969 + 3 ^ 40 * 3057582 * 2
def baseEnd_3057582 : Nat := 1570009206535561430063443

theorem tailTrace_3057582 : CollatzResearch.WordTrace tailWord_3057582 prefixEnd_3057582 1570009206535561430063443 := by
  unfold tailWord_3057582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939897151113760284595875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74346118139273388184511333 13939897151113760284595875)
  ·
    refine ⟨20909845726670640426893813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13939897151113760284595875 20909845726670640426893813)
    ·
      refine ⟨1960298036875372540021295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20909845726670640426893813 1960298036875372540021295)
      ·
        refine ⟨2940447055313058810031943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960298036875372540021295 2940447055313058810031943)
        ·
          refine ⟨4410670582969588215047915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940447055313058810031943 4410670582969588215047915)
          ·
            refine ⟨6616005874454382322571873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410670582969588215047915 6616005874454382322571873)
            ·
              refine ⟨4962004405840786741928905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6616005874454382322571873 4962004405840786741928905)
              ·
                refine ⟨3721503304380590056446679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962004405840786741928905 3721503304380590056446679)
                ·
                  refine ⟨5582254956570885084670019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721503304380590056446679 5582254956570885084670019)
                  ·
                    refine ⟨8373382434856327627005029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582254956570885084670019 8373382434856327627005029)
                    ·
                      refine ⟨1570009206535561430063443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8373382434856327627005029 1570009206535561430063443)
                      ·
                        rfl

theorem cell23_3057582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3057582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057582 prefixEnd_3057582 := by exact prefixLift 3057582
  have htrace : WordTrace (prefixWord ++ tailWord_3057582) baseStart_3057582 baseEnd_3057582 := by
    simpa [prefixWord, tailWord_3057582, baseEnd_3057582] using wordTrace_append hprefix tailTrace_3057582
  have hstable : (prefixWord ++ tailWord_3057582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057582).length < 2 ^ (prefixWord ++ tailWord_3057582).sum := by decide
  have hdescent : baseEnd_3057582 < baseStart_3057582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057608 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_3057608 : Nat := 118140960795 + 3057608 * 2 ^ 59
def prefixEnd_3057608 : Nat := 4983230072969 + 3 ^ 40 * 3057608 * 2
def baseEnd_3057608 : Nat := 1570022557032578328338323

theorem tailTrace_3057608 : CollatzResearch.WordTrace tailWord_3057608 prefixEnd_3057608 1570022557032578328338323 := by
  unfold tailWord_3057608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55760062753407944358606739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74346750337877259144808985 55760062753407944358606739)
  ·
    refine ⟨83640094130111916537910109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55760062753407944358606739 83640094130111916537910109)
    ·
      refine ⟨31365035298791968701716291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83640094130111916537910109 31365035298791968701716291)
      ·
        refine ⟨47047552948187953052574437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31365035298791968701716291 47047552948187953052574437)
        ·
          refine ⟨8821416177785241197357707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47047552948187953052574437 8821416177785241197357707)
          ·
            refine ⟨13232124266677861796036561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8821416177785241197357707 13232124266677861796036561)
            ·
              refine ⟨9924093200008396347027421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13232124266677861796036561 9924093200008396347027421)
              ·
                refine ⟨3721534950003148630135283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9924093200008396347027421 3721534950003148630135283)
                ·
                  refine ⟨5582302425004722945202925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721534950003148630135283 5582302425004722945202925)
                  ·
                    refine ⟨2093363409376771104451097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5582302425004722945202925 2093363409376771104451097)
                    ·
                      refine ⟨1570022557032578328338323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093363409376771104451097 1570022557032578328338323)
                      ·
                        rfl

theorem cell23_3057608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_3057608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057608 prefixEnd_3057608 := by exact prefixLift 3057608
  have htrace : WordTrace (prefixWord ++ tailWord_3057608) baseStart_3057608 baseEnd_3057608 := by
    simpa [prefixWord, tailWord_3057608, baseEnd_3057608] using wordTrace_append hprefix tailTrace_3057608
  have hstable : (prefixWord ++ tailWord_3057608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057608).length < 2 ^ (prefixWord ++ tailWord_3057608).sum := by decide
  have hdescent : baseEnd_3057608 < baseStart_3057608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057617 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_3057617 : Nat := 118140960795 + 3057617 * 2 ^ 59
def prefixEnd_3057617 : Nat := 4983230072969 + 3 ^ 40 * 3057617 * 2
def baseEnd_3057617 : Nat := 1570027178358468793125781

theorem tailTrace_3057617 : CollatzResearch.WordTrace tailWord_3057617 prefixEnd_3057617 1570027178358468793125781 := by
  unfold tailWord_3057617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111520453763783283254291105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74346969175855522169527403 111520453763783283254291105)
  ·
    refine ⟨83640340322837462440718329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111520453763783283254291105 83640340322837462440718329)
    ·
      refine ⟨62730255242128096830538747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83640340322837462440718329 62730255242128096830538747)
      ·
        refine ⟨94095382863192145245808121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62730255242128096830538747 94095382863192145245808121)
        ·
          refine ⟨70571537147394108934356091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94095382863192145245808121 70571537147394108934356091)
          ·
            refine ⟨105857305721091163401534137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70571537147394108934356091 105857305721091163401534137)
            ·
              refine ⟨79392979290818372551150603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105857305721091163401534137 79392979290818372551150603)
              ·
                refine ⟨119089468936227558826725905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79392979290818372551150603 119089468936227558826725905)
                ·
                  refine ⟨89317101702170669120044429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119089468936227558826725905 89317101702170669120044429)
                  ·
                    refine ⟨33493913138314000920016661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89317101702170669120044429 33493913138314000920016661)
                    ·
                      refine ⟨1570027178358468793125781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33493913138314000920016661 1570027178358468793125781)
                      ·
                        rfl

theorem cell23_3057617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_3057617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057617 prefixEnd_3057617 := by exact prefixLift 3057617
  have htrace : WordTrace (prefixWord ++ tailWord_3057617) baseStart_3057617 baseEnd_3057617 := by
    simpa [prefixWord, tailWord_3057617, baseEnd_3057617] using wordTrace_append hprefix tailTrace_3057617
  have hstable : (prefixWord ++ tailWord_3057617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057617).length < 2 ^ (prefixWord ++ tailWord_3057617).sum := by decide
  have hdescent : baseEnd_3057617 < baseStart_3057617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057624 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3057624 : Nat := 118140960795 + 3057624 * 2 ^ 59
def prefixEnd_3057624 : Nat := 4983230072969 + 3 ^ 40 * 3057624 * 2
def baseEnd_3057624 : Nat := 1570030772723050265738249

theorem tailTrace_3057624 : CollatzResearch.WordTrace tailWord_3057624 prefixEnd_3057624 1570030772723050265738249 := by
  unfold tailWord_3057624
  simp only [CollatzResearch.WordTrace]
  refine ⟨55760354537378961724897963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74347139383171948966530617 55760354537378961724897963)
  ·
    refine ⟨83640531806068442587346945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55760354537378961724897963 83640531806068442587346945)
    ·
      refine ⟨62730398854551331940510209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83640531806068442587346945 62730398854551331940510209)
      ·
        refine ⟨47047799140913498955382657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62730398854551331940510209 47047799140913498955382657)
        ·
          refine ⟨35285849355685124216536993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47047799140913498955382657 35285849355685124216536993)
          ·
            refine ⟨26464387016763843162402745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35285849355685124216536993 26464387016763843162402745)
            ·
              refine ⟨19848290262572882371802059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26464387016763843162402745 19848290262572882371802059)
              ·
                refine ⟨29772435393859323557703089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848290262572882371802059 29772435393859323557703089)
                ·
                  refine ⟨22329326545394492668277317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29772435393859323557703089 22329326545394492668277317)
                  ·
                    refine ⟨4186748727261467375301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22329326545394492668277317 4186748727261467375301997)
                    ·
                      refine ⟨1570030772723050265738249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186748727261467375301997 1570030772723050265738249)
                      ·
                        rfl

theorem cell23_3057624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3057624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057624 prefixEnd_3057624 := by exact prefixLift 3057624
  have htrace : WordTrace (prefixWord ++ tailWord_3057624) baseStart_3057624 baseEnd_3057624 := by
    simpa [prefixWord, tailWord_3057624, baseEnd_3057624] using wordTrace_append hprefix tailTrace_3057624
  have hstable : (prefixWord ++ tailWord_3057624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057624).length < 2 ^ (prefixWord ++ tailWord_3057624).sum := by decide
  have hdescent : baseEnd_3057624 < baseStart_3057624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057724 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3057724 : Nat := 118140960795 + 3057724 * 2 ^ 59
def prefixEnd_3057724 : Nat := 4983230072969 + 3 ^ 40 * 3057724 * 2
def baseEnd_3057724 : Nat := 1570082120788499874487789

theorem tailTrace_3057724 : CollatzResearch.WordTrace tailWord_3057724 prefixEnd_3057724 1570082120788499874487789 := by
  unfold tailWord_3057724
  simp only [CollatzResearch.WordTrace]
  refine ⟨55762178187197820264218113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74349570916263760352290817 55762178187197820264218113)
  ·
    refine ⟨41821633640398365198163585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55762178187197820264218113 41821633640398365198163585)
    ·
      refine ⟨31366225230298773898622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41821633640398365198163585 31366225230298773898622689)
      ·
        refine ⟨23524668922724080423967017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31366225230298773898622689 23524668922724080423967017)
        ·
          refine ⟨17643501692043060317975263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23524668922724080423967017 17643501692043060317975263)
          ·
            refine ⟨26465252538064590476962895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643501692043060317975263 26465252538064590476962895)
            ·
              refine ⟨39697878807096885715444343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26465252538064590476962895 39697878807096885715444343)
              ·
                refine ⟨59546818210645328573166515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39697878807096885715444343 59546818210645328573166515)
                ·
                  refine ⟨89320227315967992859749773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59546818210645328573166515 89320227315967992859749773)
                  ·
                    refine ⟨33495085243487997322406165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89320227315967992859749773 33495085243487997322406165)
                    ·
                      refine ⟨1570082120788499874487789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33495085243487997322406165 1570082120788499874487789)
                      ·
                        rfl

theorem cell23_3057724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3057724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057724 prefixEnd_3057724 := by exact prefixLift 3057724
  have htrace : WordTrace (prefixWord ++ tailWord_3057724) baseStart_3057724 baseEnd_3057724 := by
    simpa [prefixWord, tailWord_3057724, baseEnd_3057724] using wordTrace_append hprefix tailTrace_3057724
  have hstable : (prefixWord ++ tailWord_3057724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057724).length < 2 ^ (prefixWord ++ tailWord_3057724).sum := by decide
  have hdescent : baseEnd_3057724 < baseStart_3057724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057741 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3057741 : Nat := 118140960795 + 3057741 * 2 ^ 59
def prefixEnd_3057741 : Nat := 4983230072969 + 3 ^ 40 * 3057741 * 2
def baseEnd_3057741 : Nat := 1570090849959626307975211

theorem tailTrace_3057741 : CollatzResearch.WordTrace tailWord_3057741 prefixEnd_3057741 1570090849959626307975211 := by
  unfold tailWord_3057741
  simp only [CollatzResearch.WordTrace]
  refine ⟨111524976415334052431805077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74349984276889368287870051 111524976415334052431805077)
  ·
    refine ⟨5227733269468783707740863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111524976415334052431805077 5227733269468783707740863)
    ·
      refine ⟨7841599904203175561611295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227733269468783707740863 7841599904203175561611295)
      ·
        refine ⟨11762399856304763342416943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841599904203175561611295 11762399856304763342416943)
        ·
          refine ⟨17643599784457145013625415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762399856304763342416943 17643599784457145013625415)
          ·
            refine ⟨26465399676685717520438123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643599784457145013625415 26465399676685717520438123)
            ·
              refine ⟨39698099515028576280657185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26465399676685717520438123 39698099515028576280657185)
              ·
                refine ⟨29773574636271432210492889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39698099515028576280657185 29773574636271432210492889)
                ·
                  refine ⟨22330180977203574157869667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29773574636271432210492889 22330180977203574157869667)
                  ·
                    refine ⟨33495271465805361236804501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22330180977203574157869667 33495271465805361236804501)
                    ·
                      refine ⟨1570090849959626307975211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33495271465805361236804501 1570090849959626307975211)
                      ·
                        rfl

theorem cell23_3057741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3057741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057741 prefixEnd_3057741 := by exact prefixLift 3057741
  have htrace : WordTrace (prefixWord ++ tailWord_3057741) baseStart_3057741 baseEnd_3057741 := by
    simpa [prefixWord, tailWord_3057741, baseEnd_3057741] using wordTrace_append hprefix tailTrace_3057741
  have hstable : (prefixWord ++ tailWord_3057741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057741).length < 2 ^ (prefixWord ++ tailWord_3057741).sum := by decide
  have hdescent : baseEnd_3057741 < baseStart_3057741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057754 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3057754 : Nat := 118140960795 + 3057754 * 2 ^ 59
def prefixEnd_3057754 : Nat := 4983230072969 + 3 ^ 40 * 3057754 * 2
def baseEnd_3057754 : Nat := 1570097525208134757112651

theorem tailTrace_3057754 : CollatzResearch.WordTrace tailWord_3057754 prefixEnd_3057754 1570097525208134757112651 := by
  unfold tailWord_3057754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881362641071738913007079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74350300376191303768018877 27881362641071738913007079)
  ·
    refine ⟨41822043961607608369510619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27881362641071738913007079 41822043961607608369510619)
    ·
      refine ⟨62733065942411412554265929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41822043961607608369510619 62733065942411412554265929)
      ·
        refine ⟨47049799456808559415699447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62733065942411412554265929 47049799456808559415699447)
        ·
          refine ⟨70574699185212839123549171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47049799456808559415699447 70574699185212839123549171)
          ·
            refine ⟨105862048777819258685323757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70574699185212839123549171 105862048777819258685323757)
            ·
              refine ⟨39698268291682222006996409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105862048777819258685323757 39698268291682222006996409)
              ·
                refine ⟨29773701218761666505247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39698268291682222006996409 29773701218761666505247307)
                ·
                  refine ⟨44660551828142499757870961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29773701218761666505247307 44660551828142499757870961)
                  ·
                    refine ⟨33495413871106874818403221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44660551828142499757870961 33495413871106874818403221)
                    ·
                      refine ⟨1570097525208134757112651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33495413871106874818403221 1570097525208134757112651)
                      ·
                        rfl

theorem cell23_3057754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3057754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057754 prefixEnd_3057754 := by exact prefixLift 3057754
  have htrace : WordTrace (prefixWord ++ tailWord_3057754) baseStart_3057754 baseEnd_3057754 := by
    simpa [prefixWord, tailWord_3057754, baseEnd_3057754] using wordTrace_append hprefix tailTrace_3057754
  have hstable : (prefixWord ++ tailWord_3057754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057754).length < 2 ^ (prefixWord ++ tailWord_3057754).sum := by decide
  have hdescent : baseEnd_3057754 < baseStart_3057754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057788 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_3057788 : Nat := 118140960795 + 3057788 * 2 ^ 59
def prefixEnd_3057788 : Nat := 4983230072969 + 3 ^ 40 * 3057788 * 2
def baseEnd_3057788 : Nat := 1570114983550387624087495

theorem tailTrace_3057788 : CollatzResearch.WordTrace tailWord_3057788 prefixEnd_3057788 1570114983550387624087495 := by
  unfold tailWord_3057788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55763345323081889729383009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74351127097442519639177345 55763345323081889729383009)
  ·
    refine ⟨41822508992311417297037257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55763345323081889729383009 41822508992311417297037257)
    ·
      refine ⟨31366881744233562972777943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41822508992311417297037257 31366881744233562972777943)
      ·
        refine ⟨47050322616350344459166915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31366881744233562972777943 47050322616350344459166915)
        ·
          refine ⟨70575483924525516688750373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47050322616350344459166915 70575483924525516688750373)
          ·
            refine ⟨13232903235848534379140695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70575483924525516688750373 13232903235848534379140695)
            ·
              refine ⟨19849354853772801568711043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13232903235848534379140695 19849354853772801568711043)
              ·
                refine ⟨29774032280659202353066565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19849354853772801568711043 29774032280659202353066565)
                ·
                  refine ⟨5582631052623600441199981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29774032280659202353066565 5582631052623600441199981)
                  ·
                    refine ⟨2093486644733850165449993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5582631052623600441199981 2093486644733850165449993)
                    ·
                      refine ⟨1570114983550387624087495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093486644733850165449993 1570114983550387624087495)
                      ·
                        rfl

theorem cell23_3057788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_3057788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057788 prefixEnd_3057788 := by exact prefixLift 3057788
  have htrace : WordTrace (prefixWord ++ tailWord_3057788) baseStart_3057788 baseEnd_3057788 := by
    simpa [prefixWord, tailWord_3057788, baseEnd_3057788] using wordTrace_append hprefix tailTrace_3057788
  have hstable : (prefixWord ++ tailWord_3057788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057788).length < 2 ^ (prefixWord ++ tailWord_3057788).sum := by decide
  have hdescent : baseEnd_3057788 < baseStart_3057788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057795 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 3]
def baseStart_3057795 : Nat := 118140960795 + 3057795 * 2 ^ 59
def prefixEnd_3057795 : Nat := 4983230072969 + 3 ^ 40 * 3057795 * 2
def baseEnd_3057795 : Nat := 1570118577914969096699963

theorem tailTrace_3057795 : CollatzResearch.WordTrace tailWord_3057795 prefixEnd_3057795 1570118577914969096699963 := by
  unfold tailWord_3057795
  simp only [CollatzResearch.WordTrace]
  refine ⟨111526945957138419654270839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74351297304758946436180559 111526945957138419654270839)
  ·
    refine ⟨167290418935707629481406259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111526945957138419654270839 167290418935707629481406259)
    ·
      refine ⟨250935628403561444222109389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167290418935707629481406259 250935628403561444222109389)
      ·
        refine ⟨94100860651335541583291021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250935628403561444222109389 94100860651335541583291021)
        ·
          refine ⟨35287822744250828093734133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94100860651335541583291021 35287822744250828093734133)
          ·
            refine ⟨3308233382273515133787575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35287822744250828093734133 3308233382273515133787575)
            ·
              refine ⟨4962350073410272700681363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308233382273515133787575 4962350073410272700681363)
              ·
                refine ⟨7443525110115409051022045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962350073410272700681363 7443525110115409051022045)
                ·
                  refine ⟨2791321916293278394133267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7443525110115409051022045 2791321916293278394133267)
                  ·
                    refine ⟨4186982874439917591199901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2791321916293278394133267 4186982874439917591199901)
                    ·
                      refine ⟨1570118577914969096699963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186982874439917591199901 1570118577914969096699963)
                      ·
                        rfl

theorem cell23_3057795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_3057795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057795 prefixEnd_3057795 := by exact prefixLift 3057795
  have htrace : WordTrace (prefixWord ++ tailWord_3057795) baseStart_3057795 baseEnd_3057795 := by
    simpa [prefixWord, tailWord_3057795, baseEnd_3057795] using wordTrace_append hprefix tailTrace_3057795
  have hstable : (prefixWord ++ tailWord_3057795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057795).length < 2 ^ (prefixWord ++ tailWord_3057795).sum := by decide
  have hdescent : baseEnd_3057795 < baseStart_3057795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057801 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_3057801 : Nat := 118140960795 + 3057801 * 2 ^ 59
def prefixEnd_3057801 : Nat := 4983230072969 + 3 ^ 40 * 3057801 * 2
def baseEnd_3057801 : Nat := 1570121658798896073224935

theorem tailTrace_3057801 : CollatzResearch.WordTrace tailWord_3057801 prefixEnd_3057801 1570121658798896073224935 := by
  unfold tailWord_3057801
  simp only [CollatzResearch.WordTrace]
  refine ⟨111527164795116682678989257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74351443196744455119326171 111527164795116682678989257)
  ·
    refine ⟨83645373596337512009241943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111527164795116682678989257 83645373596337512009241943)
    ·
      refine ⟨125468060394506268013862915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83645373596337512009241943 125468060394506268013862915)
      ·
        refine ⟨188202090591759402020794373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125468060394506268013862915 188202090591759402020794373)
        ·
          refine ⟨35287891985954887878898945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188202090591759402020794373 35287891985954887878898945)
          ·
            refine ⟨26465918989466165909174209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35287891985954887878898945 26465918989466165909174209)
            ·
              refine ⟨19849439242099624431880657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26465918989466165909174209 19849439242099624431880657)
              ·
                refine ⟨14887079431574718323910493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19849439242099624431880657 14887079431574718323910493)
                ·
                  refine ⟨5582654786840519371466435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14887079431574718323910493 5582654786840519371466435)
                  ·
                    refine ⟨8373982180260779057199653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582654786840519371466435 8373982180260779057199653)
                    ·
                      refine ⟨1570121658798896073224935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8373982180260779057199653 1570121658798896073224935)
                      ·
                        rfl

theorem cell23_3057801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_3057801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057801 prefixEnd_3057801 := by exact prefixLift 3057801
  have htrace : WordTrace (prefixWord ++ tailWord_3057801) baseStart_3057801 baseEnd_3057801 := by
    simpa [prefixWord, tailWord_3057801, baseEnd_3057801] using wordTrace_append hprefix tailTrace_3057801
  have hstable : (prefixWord ++ tailWord_3057801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057801).length < 2 ^ (prefixWord ++ tailWord_3057801).sum := by decide
  have hdescent : baseEnd_3057801 < baseStart_3057801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057815 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 1, 5]
def baseStart_3057815 : Nat := 118140960795 + 3057815 * 2 ^ 59
def prefixEnd_3057815 : Nat := 4983230072969 + 3 ^ 40 * 3057815 * 2
def baseEnd_3057815 : Nat := 523376282509353006149957

theorem tailTrace_3057815 : CollatzResearch.WordTrace tailWord_3057815 prefixEnd_3057815 523376282509353006149957 := by
  unfold tailWord_3057815
  simp only [CollatzResearch.WordTrace]
  refine ⟨111527675417065963069998899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74351783611377308713332599 111527675417065963069998899)
  ·
    refine ⟨167291513125598944604998349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111527675417065963069998899 167291513125598944604998349)
    ·
      refine ⟨62734317422099604226874381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167291513125598944604998349 62734317422099604226874381)
      ·
        refine ⟨23525369033287351585077893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62734317422099604226874381 23525369033287351585077893)
        ·
          refine ⟨4411006693741378422202105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23525369033287351585077893 4411006693741378422202105)
          ·
            refine ⟨3308255020306033816651579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4411006693741378422202105 3308255020306033816651579)
            ·
              refine ⟨4962382530459050724977369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308255020306033816651579 4962382530459050724977369)
              ·
                refine ⟨3721786897844288043733027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962382530459050724977369 3721786897844288043733027)
                ·
                  refine ⟨5582680346766432065599541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721786897844288043733027 5582680346766432065599541)
                  ·
                    refine ⟨523376282509353006149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5582680346766432065599541 523376282509353006149957)
                    ·
                      rfl

theorem cell23_3057815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_3057815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057815 prefixEnd_3057815 := by exact prefixLift 3057815
  have htrace : WordTrace (prefixWord ++ tailWord_3057815) baseStart_3057815 baseEnd_3057815 := by
    simpa [prefixWord, tailWord_3057815, baseEnd_3057815] using wordTrace_append hprefix tailTrace_3057815
  have hstable : (prefixWord ++ tailWord_3057815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057815).length < 2 ^ (prefixWord ++ tailWord_3057815).sum := by decide
  have hdescent : baseEnd_3057815 < baseStart_3057815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057828 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_3057828 : Nat := 118140960795 + 3057828 * 2 ^ 59
def prefixEnd_3057828 : Nat := 4983230072969 + 3 ^ 40 * 3057828 * 2
def baseEnd_3057828 : Nat := 523378507592189155862437

theorem tailTrace_3057828 : CollatzResearch.WordTrace tailWord_3057828 prefixEnd_3057828 523378507592189155862437 := by
  unfold tailWord_3057828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764074783009433145111069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74352099710679244193481425 55764074783009433145111069)
  ·
    refine ⟨20911528043628537429416651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55764074783009433145111069 20911528043628537429416651)
    ·
      refine ⟨31367292065442806144124977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20911528043628537429416651 31367292065442806144124977)
      ·
        refine ⟨23525469049082104608093733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31367292065442806144124977 23525469049082104608093733)
        ·
          refine ⟨4411025446702894614017575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23525469049082104608093733 4411025446702894614017575)
          ·
            refine ⟨6616538170054341921026363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411025446702894614017575 6616538170054341921026363)
            ·
              refine ⟨9924807255081512881539545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616538170054341921026363 9924807255081512881539545)
              ·
                refine ⟨7443605441311134661154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9924807255081512881539545 7443605441311134661154659)
                ·
                  refine ⟨11165408161966701991731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443605441311134661154659 11165408161966701991731989)
                  ·
                    refine ⟨523378507592189155862437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11165408161966701991731989 523378507592189155862437)
                    ·
                      rfl

theorem cell23_3057828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_3057828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057828 prefixEnd_3057828 := by exact prefixLift 3057828
  have htrace : WordTrace (prefixWord ++ tailWord_3057828) baseStart_3057828 baseEnd_3057828 := by
    simpa [prefixWord, tailWord_3057828, baseEnd_3057828] using wordTrace_append hprefix tailTrace_3057828
  have hstable : (prefixWord ++ tailWord_3057828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057828).length < 2 ^ (prefixWord ++ tailWord_3057828).sum := by decide
  have hdescent : baseEnd_3057828 < baseStart_3057828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057841 : List Nat := [1, 2, 2, 5, 2, 11]
def baseStart_3057841 : Nat := 118140960795 + 3057841 * 2 ^ 59
def prefixEnd_3057841 : Nat := 4983230072969 + 3 ^ 40 * 3057841 * 2
def baseEnd_3057841 : Nat := 6461490526852164266357

theorem tailTrace_3057841 : CollatzResearch.WordTrace tailWord_3057841 prefixEnd_3057841 6461490526852164266357 := by
  unfold tailWord_3057841
  simp only [CollatzResearch.WordTrace]
  refine ⟨111528623714971769510445377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74352415809981179673630251 111528623714971769510445377)
  ·
    refine ⟨83646467786228827132834033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111528623714971769510445377 83646467786228827132834033)
    ·
      refine ⟨62734850839671620349625525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83646467786228827132834033 62734850839671620349625525)
      ·
        refine ⟨5881392266219214407777393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62734850839671620349625525 5881392266219214407777393)
        ·
          refine ⟨4411044199664410805833045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881392266219214407777393 4411044199664410805833045)
          ·
            refine ⟨6461490526852164266357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4411044199664410805833045 6461490526852164266357)
            ·
              rfl

theorem cell23_3057841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 11].length) (baseStart_3057841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057841 prefixEnd_3057841 := by exact prefixLift 3057841
  have htrace : WordTrace (prefixWord ++ tailWord_3057841) baseStart_3057841 baseEnd_3057841 := by
    simpa [prefixWord, tailWord_3057841, baseEnd_3057841] using wordTrace_append hprefix tailTrace_3057841
  have hstable : (prefixWord ++ tailWord_3057841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057841).length < 2 ^ (prefixWord ++ tailWord_3057841).sum := by decide
  have hdescent : baseEnd_3057841 < baseStart_3057841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057851 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3]
def baseStart_3057851 : Nat := 118140960795 + 3057851 * 2 ^ 59
def prefixEnd_3057851 : Nat := 4983230072969 + 3 ^ 40 * 3057851 * 2
def baseEnd_3057851 : Nat := 1570147332831620877599705

theorem tailTrace_3057851 : CollatzResearch.WordTrace tailWord_3057851 prefixEnd_3057851 1570147332831620877599705 := by
  unfold tailWord_3057851
  simp only [CollatzResearch.WordTrace]
  refine ⟨111528988444935541218309407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74352658963290360812206271 111528988444935541218309407)
  ·
    refine ⟨167293482667403311827464111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111528988444935541218309407 167293482667403311827464111)
    ·
      refine ⟨250940224001104967741196167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167293482667403311827464111 250940224001104967741196167)
      ·
        refine ⟨376410336001657451611794251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250940224001104967741196167 376410336001657451611794251)
        ·
          refine ⟨564615504002486177417691377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376410336001657451611794251 564615504002486177417691377)
          ·
            refine ⟨423461628001864633063268533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564615504002486177417691377 423461628001864633063268533)
            ·
              refine ⟨39699527625174809349681425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 423461628001864633063268533 39699527625174809349681425)
              ·
                refine ⟨29774645718881107012261069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39699527625174809349681425 29774645718881107012261069)
                ·
                  refine ⟨11165492144580415129597901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29774645718881107012261069 11165492144580415129597901)
                  ·
                    refine ⟨4187059554217655673599213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165492144580415129597901 4187059554217655673599213)
                    ·
                      refine ⟨1570147332831620877599705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187059554217655673599213 1570147332831620877599705)
                      ·
                        rfl

theorem cell23_3057851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].length) (baseStart_3057851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057851 prefixEnd_3057851 := by exact prefixLift 3057851
  have htrace : WordTrace (prefixWord ++ tailWord_3057851) baseStart_3057851 baseEnd_3057851 := by
    simpa [prefixWord, tailWord_3057851, baseEnd_3057851] using wordTrace_append hprefix tailTrace_3057851
  have hstable : (prefixWord ++ tailWord_3057851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057851).length < 2 ^ (prefixWord ++ tailWord_3057851).sum := by decide
  have hdescent : baseEnd_3057851 < baseStart_3057851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057885 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3057885 : Nat := 118140960795 + 3057885 * 2 ^ 59
def prefixEnd_3057885 : Nat := 4983230072969 + 3 ^ 40 * 3057885 * 2
def baseEnd_3057885 : Nat := 1570164791173873744574549

theorem tailTrace_3057885 : CollatzResearch.WordTrace tailWord_3057885 prefixEnd_3057885 1570164791173873744574549 := by
  unfold tailWord_3057885
  simp only [CollatzResearch.WordTrace]
  refine ⟨111530228526812365025047109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74353485684541576683364739 111530228526812365025047109)
  ·
    refine ⟨20911917848777318442196333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111530228526812365025047109 20911917848777318442196333)
    ·
      refine ⟨7841969193291494415823625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20911917848777318442196333 7841969193291494415823625)
      ·
        refine ⟨5881476894968620811867719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841969193291494415823625 5881476894968620811867719)
        ·
          refine ⟨8822215342452931217801579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881476894968620811867719 8822215342452931217801579)
          ·
            refine ⟨13233323013679396826702369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822215342452931217801579 13233323013679396826702369)
            ·
              refine ⟨9924992260259547620026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13233323013679396826702369 9924992260259547620026777)
              ·
                refine ⟨7443744195194660715020083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9924992260259547620026777 7443744195194660715020083)
                ·
                  refine ⟨11165616292791991072530125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443744195194660715020083 11165616292791991072530125)
                  ·
                    refine ⟨4187106109796996652198797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165616292791991072530125 4187106109796996652198797)
                    ·
                      refine ⟨1570164791173873744574549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187106109796996652198797 1570164791173873744574549)
                      ·
                        rfl

theorem cell23_3057885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3057885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057885 prefixEnd_3057885 := by exact prefixLift 3057885
  have htrace : WordTrace (prefixWord ++ tailWord_3057885) baseStart_3057885 baseEnd_3057885 := by
    simpa [prefixWord, tailWord_3057885, baseEnd_3057885] using wordTrace_append hprefix tailTrace_3057885
  have hstable : (prefixWord ++ tailWord_3057885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057885).length < 2 ^ (prefixWord ++ tailWord_3057885).sum := by decide
  have hdescent : baseEnd_3057885 < baseStart_3057885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057918 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3057918 : Nat := 118140960795 + 3057918 * 2 ^ 59
def prefixEnd_3057918 : Nat := 4983230072969 + 3 ^ 40 * 3057918 * 2
def baseEnd_3057918 : Nat := 523393912011824038487299

theorem tailTrace_3057918 : CollatzResearch.WordTrace tailWord_3057918 prefixEnd_3057918 523393912011824038487299 := by
  unfold tailWord_3057918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941429016961601457624801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74354288090461874440665605 13941429016961601457624801)
  ·
    refine ⟨10456071762721201093218601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13941429016961601457624801 10456071762721201093218601)
    ·
      refine ⟨7842053822040900819913951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10456071762721201093218601 7842053822040900819913951)
      ·
        refine ⟨11763080733061351229870927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7842053822040900819913951 11763080733061351229870927)
        ·
          refine ⟨17644621099592026844806391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11763080733061351229870927 17644621099592026844806391)
          ·
            refine ⟨26466931649388040267209587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17644621099592026844806391 26466931649388040267209587)
            ·
              refine ⟨39700397474082060400814381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26466931649388040267209587 39700397474082060400814381)
              ·
                refine ⟨14887649052780772650305393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39700397474082060400814381 14887649052780772650305393)
                ·
                  refine ⟨11165736789585579487729045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14887649052780772650305393 11165736789585579487729045)
                  ·
                    refine ⟨523393912011824038487299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11165736789585579487729045 523393912011824038487299)
                    ·
                      rfl

theorem cell23_3057918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3057918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057918 prefixEnd_3057918 := by exact prefixLift 3057918
  have htrace : WordTrace (prefixWord ++ tailWord_3057918) baseStart_3057918 baseEnd_3057918 := by
    simpa [prefixWord, tailWord_3057918, baseEnd_3057918] using wordTrace_append hprefix tailTrace_3057918
  have hstable : (prefixWord ++ tailWord_3057918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057918).length < 2 ^ (prefixWord ++ tailWord_3057918).sum := by decide
  have hdescent : baseEnd_3057918 < baseStart_3057918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057931 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 7]
def baseStart_3057931 : Nat := 118140960795 + 3057931 * 2 ^ 59
def prefixEnd_3057931 : Nat := 4983230072969 + 3 ^ 40 * 3057931 * 2
def baseEnd_3057931 : Nat := 174465379031553396066593

theorem tailTrace_3057931 : CollatzResearch.WordTrace tailWord_3057931 prefixEnd_3057931 174465379031553396066593 := by
  unfold tailWord_3057931
  simp only [CollatzResearch.WordTrace]
  refine ⟨111531906284645714881221647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74354604189763809920814431 111531906284645714881221647)
  ·
    refine ⟨167297859426968572321832471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111531906284645714881221647 167297859426968572321832471)
    ·
      refine ⟨250946789140452858482748707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167297859426968572321832471 250946789140452858482748707)
      ·
        refine ⟨376420183710679287724123061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250946789140452858482748707 376420183710679287724123061)
        ·
          refine ⟨35289392222876183224136537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 376420183710679287724123061 35289392222876183224136537)
          ·
            refine ⟨26467044167157137418102403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35289392222876183224136537 26467044167157137418102403)
            ·
              refine ⟨39700566250735706127153605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26467044167157137418102403 39700566250735706127153605)
              ·
                refine ⟨7443856172012944898841301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39700566250735706127153605 7443856172012944898841301)
                ·
                  refine ⟨174465379031553396066593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7443856172012944898841301 174465379031553396066593)
                  ·
                    rfl

theorem cell23_3057931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 7].length) (baseStart_3057931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057931 prefixEnd_3057931 := by exact prefixLift 3057931
  have htrace : WordTrace (prefixWord ++ tailWord_3057931) baseStart_3057931 baseEnd_3057931 := by
    simpa [prefixWord, tailWord_3057931, baseEnd_3057931] using wordTrace_append hprefix tailTrace_3057931
  have hstable : (prefixWord ++ tailWord_3057931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057931).length < 2 ^ (prefixWord ++ tailWord_3057931).sum := by decide
  have hdescent : baseEnd_3057931 < baseStart_3057931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058008 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_3058008 : Nat := 118140960795 + 3058008 * 2 ^ 59
def prefixEnd_3058008 : Nat := 4983230072969 + 3 ^ 40 * 3058008 * 2
def baseEnd_3058008 : Nat := 523409316431458921112161

theorem tailTrace_3058008 : CollatzResearch.WordTrace tailWord_3058008 prefixEnd_3058008 523409316431458921112161 := by
  unfold tailWord_3058008
  simp only [CollatzResearch.WordTrace]
  refine ⟨55767357352683378515887339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74356476470244504687849785 55767357352683378515887339)
  ·
    refine ⟨83651036029025067773831009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55767357352683378515887339 83651036029025067773831009)
    ·
      refine ⟨62738277021768800830373257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83651036029025067773831009 62738277021768800830373257)
      ·
        refine ⟨47053707766326600622779943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62738277021768800830373257 47053707766326600622779943)
        ·
          refine ⟨70580561649489900934169915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47053707766326600622779943 70580561649489900934169915)
          ·
            refine ⟨105870842474234851401254873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70580561649489900934169915 105870842474234851401254873)
            ·
              refine ⟨79403131855676138550941155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105870842474234851401254873 79403131855676138550941155)
              ·
                refine ⟨119104697783514207826411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79403131855676138550941155 119104697783514207826411733)
                ·
                  refine ⟨2791516354301114245931525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119104697783514207826411733 2791516354301114245931525)
                  ·
                    refine ⟨523409316431458921112161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791516354301114245931525 523409316431458921112161)
                    ·
                      rfl

theorem cell23_3058008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_3058008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058008 prefixEnd_3058008 := by exact prefixLift 3058008
  have htrace : WordTrace (prefixWord ++ tailWord_3058008) baseStart_3058008 baseEnd_3058008 := by
    simpa [prefixWord, tailWord_3058008, baseEnd_3058008] using wordTrace_append hprefix tailTrace_3058008
  have hstable : (prefixWord ++ tailWord_3058008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058008).length < 2 ^ (prefixWord ++ tailWord_3058008).sum := by decide
  have hdescent : baseEnd_3058008 < baseStart_3058008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058072 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 6]
def baseStart_3058072 : Nat := 118140960795 + 3058072 * 2 ^ 59
def prefixEnd_3058072 : Nat := 4983230072969 + 3 ^ 40 * 3058072 * 2
def baseEnd_3058072 : Nat := 174473423561807168104021

theorem tailTrace_3058072 : CollatzResearch.WordTrace tailWord_3058072 prefixEnd_3058072 174473423561807168104021 := by
  unfold tailWord_3058072
  simp only [CollatzResearch.WordTrace]
  refine ⟨55768524488567447981052235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74358032651423263974736313 55768524488567447981052235)
  ·
    refine ⟨83652786732851171971578353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55768524488567447981052235 83652786732851171971578353)
    ·
      refine ⟨62739590049638378978683765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83652786732851171971578353 62739590049638378978683765)
      ·
        refine ⟨5881836567153598029251603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62739590049638378978683765 5881836567153598029251603)
        ·
          refine ⟨8822754850730397043877405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881836567153598029251603 8822754850730397043877405)
          ·
            refine ⟨3308533069023898891454027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8822754850730397043877405 3308533069023898891454027)
            ·
              refine ⟨4962799603535848337181041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308533069023898891454027 4962799603535848337181041)
              ·
                refine ⟨3722099702651886252885781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962799603535848337181041 3722099702651886252885781)
                ·
                  refine ⟨174473423561807168104021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3722099702651886252885781 174473423561807168104021)
                  ·
                    rfl

theorem cell23_3058072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_3058072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058072 prefixEnd_3058072 := by exact prefixLift 3058072
  have htrace : WordTrace (prefixWord ++ tailWord_3058072) baseStart_3058072 baseEnd_3058072 := by
    simpa [prefixWord, tailWord_3058072, baseEnd_3058072] using wordTrace_append hprefix tailTrace_3058072
  have hstable : (prefixWord ++ tailWord_3058072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058072).length < 2 ^ (prefixWord ++ tailWord_3058072).sum := by decide
  have hdescent : baseEnd_3058072 < baseStart_3058072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058132 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3058132 : Nat := 118140960795 + 3058132 * 2 ^ 59
def prefixEnd_3058132 : Nat := 4983230072969 + 3 ^ 40 * 3058132 * 2
def baseEnd_3058132 : Nat := 523430540298511426061971

theorem tailTrace_3058132 : CollatzResearch.WordTrace tailWord_3058132 prefixEnd_3058132 523430540298511426061971 := by
  unfold tailWord_3058132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55769618678458763104644325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74359491571278350806192433 55769618678458763104644325)
  ·
    refine ⟨10456803502211018082120811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55769618678458763104644325 10456803502211018082120811)
    ·
      refine ⟨15685205253316527123181217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456803502211018082120811 15685205253316527123181217)
      ·
        refine ⟨11763903939987395342385913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685205253316527123181217 11763903939987395342385913)
        ·
          refine ⟨8822927954990546506789435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11763903939987395342385913 8822927954990546506789435)
          ·
            refine ⟨13234391932485819760184153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822927954990546506789435 13234391932485819760184153)
            ·
              refine ⟨9925793949364364820138115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13234391932485819760184153 9925793949364364820138115)
              ·
                refine ⟨14888690924046547230207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925793949364364820138115 14888690924046547230207173)
                ·
                  refine ⟨2791629548258727605663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14888690924046547230207173 2791629548258727605663845)
                  ·
                    refine ⟨523430540298511426061971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791629548258727605663845 523430540298511426061971)
                    ·
                      rfl

theorem cell23_3058132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3058132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058132 prefixEnd_3058132 := by exact prefixLift 3058132
  have htrace : WordTrace (prefixWord ++ tailWord_3058132) baseStart_3058132 baseEnd_3058132 := by
    simpa [prefixWord, tailWord_3058132, baseEnd_3058132] using wordTrace_append hprefix tailTrace_3058132
  have hstable : (prefixWord ++ tailWord_3058132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058132).length < 2 ^ (prefixWord ++ tailWord_3058132).sum := by decide
  have hdescent : baseEnd_3058132 < baseStart_3058132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058149 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_3058149 : Nat := 118140960795 + 3058149 * 2 ^ 59
def prefixEnd_3058149 : Nat := 4983230072969 + 3 ^ 40 * 3058149 * 2
def baseEnd_3058149 : Nat := 523433450022220237224445

theorem tailTrace_3058149 : CollatzResearch.WordTrace tailWord_3058149 prefixEnd_3058149 523433450022220237224445 := by
  unfold tailWord_3058149
  simp only [CollatzResearch.WordTrace]
  refine ⟨111539857397855938112657501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74359904931903958741771667 111539857397855938112657501)
  ·
    refine ⟨41827446524195976792246563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111539857397855938112657501 41827446524195976792246563)
    ·
      refine ⟨62741169786293965188369845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41827446524195976792246563 62741169786293965188369845)
      ·
        refine ⟨5881984667465059236409673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62741169786293965188369845 5881984667465059236409673)
        ·
          refine ⟨4411488500598794427307255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881984667465059236409673 4411488500598794427307255)
          ·
            refine ⟨6617232750898191640960883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411488500598794427307255 6617232750898191640960883)
            ·
              refine ⟨9925849126347287461441325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617232750898191640960883 9925849126347287461441325)
              ·
                refine ⟨3722193422380232798040497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9925849126347287461441325 3722193422380232798040497)
                ·
                  refine ⟨2791645066785174598530373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722193422380232798040497 2791645066785174598530373)
                  ·
                    refine ⟨523433450022220237224445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791645066785174598530373 523433450022220237224445)
                    ·
                      rfl

theorem cell23_3058149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_3058149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058149 prefixEnd_3058149 := by exact prefixLift 3058149
  have htrace : WordTrace (prefixWord ++ tailWord_3058149) baseStart_3058149 baseEnd_3058149 := by
    simpa [prefixWord, tailWord_3058149, baseEnd_3058149] using wordTrace_append hprefix tailTrace_3058149
  have hstable : (prefixWord ++ tailWord_3058149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058149).length < 2 ^ (prefixWord ++ tailWord_3058149).sum := by decide
  have hdescent : baseEnd_3058149 < baseStart_3058149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058155 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3]
def baseStart_3058155 : Nat := 118140960795 + 3058155 * 2 ^ 59
def prefixEnd_3058155 : Nat := 4983230072969 + 3 ^ 40 * 3058155 * 2
def baseEnd_3058155 : Nat := 1570303430950587688198307

theorem tailTrace_3058155 : CollatzResearch.WordTrace tailWord_3058155 prefixEnd_3058155 1570303430950587688198307 := by
  unfold tailWord_3058155
  simp only [CollatzResearch.WordTrace]
  refine ⟨111540076235834201137375919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74360050823889467424917279 111540076235834201137375919)
  ·
    refine ⟨167310114353751301706063879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111540076235834201137375919 167310114353751301706063879)
    ·
      refine ⟨250965171530626952559095819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167310114353751301706063879 250965171530626952559095819)
      ·
        refine ⟨376447757295940428838643729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250965171530626952559095819 376447757295940428838643729)
        ·
          refine ⟨282335817971955321628982797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376447757295940428838643729 282335817971955321628982797)
          ·
            refine ⟨105875931739483245610868549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282335817971955321628982797 105875931739483245610868549)
            ·
              refine ⟨19851737201153108552037853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105875931739483245610868549 19851737201153108552037853)
              ·
                refine ⟨7444401450432415707014195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19851737201153108552037853 7444401450432415707014195)
                ·
                  refine ⟨11166602175648623560521293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444401450432415707014195 11166602175648623560521293)
                  ·
                    refine ⟨4187475815868233835195485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11166602175648623560521293 4187475815868233835195485)
                    ·
                      refine ⟨1570303430950587688198307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187475815868233835195485 1570303430950587688198307)
                      ·
                        rfl

theorem cell23_3058155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].length) (baseStart_3058155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058155 prefixEnd_3058155 := by exact prefixLift 3058155
  have htrace : WordTrace (prefixWord ++ tailWord_3058155) baseStart_3058155 baseEnd_3058155 := by
    simpa [prefixWord, tailWord_3058155, baseEnd_3058155] using wordTrace_append hprefix tailTrace_3058155
  have hstable : (prefixWord ++ tailWord_3058155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058155).length < 2 ^ (prefixWord ++ tailWord_3058155).sum := by decide
  have hdescent : baseEnd_3058155 < baseStart_3058155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058190 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3058190 : Nat := 118140960795 + 3058190 * 2 ^ 59
def prefixEnd_3058190 : Nat := 4983230072969 + 3 ^ 40 * 3058190 * 2
def baseEnd_3058190 : Nat := 1570321402773495051260647

theorem tailTrace_3058190 : CollatzResearch.WordTrace tailWord_3058190 prefixEnd_3058190 1570321402773495051260647 := by
  unfold tailWord_3058190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942669098838425264362503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74360901860471601409933349 13942669098838425264362503)
  ·
    refine ⟨20914003648257637896543755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13942669098838425264362503 20914003648257637896543755)
    ·
      refine ⟨31371005472386456844815633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20914003648257637896543755 31371005472386456844815633)
      ·
        refine ⟨23528254104289842633611725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31371005472386456844815633 23528254104289842633611725)
        ·
          refine ⟨8823095289108690987604397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23528254104289842633611725 8823095289108690987604397)
          ·
            refine ⟨3308660733415759120351649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8823095289108690987604397 3308660733415759120351649)
            ·
              refine ⟨2481495550061819340263737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3308660733415759120351649 2481495550061819340263737)
              ·
                refine ⟨1861121662546364505197803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481495550061819340263737 1861121662546364505197803)
                ·
                  refine ⟨2791682493819546757796705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861121662546364505197803 2791682493819546757796705)
                  ·
                    refine ⟨2093761870364660068347529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791682493819546757796705 2093761870364660068347529)
                    ·
                      refine ⟨1570321402773495051260647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093761870364660068347529 1570321402773495051260647)
                      ·
                        rfl

theorem cell23_3058190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3058190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058190 prefixEnd_3058190 := by exact prefixLift 3058190
  have htrace : WordTrace (prefixWord ++ tailWord_3058190) baseStart_3058190 baseEnd_3058190 := by
    simpa [prefixWord, tailWord_3058190, baseEnd_3058190] using wordTrace_append hprefix tailTrace_3058190
  have hstable : (prefixWord ++ tailWord_3058190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058190).length < 2 ^ (prefixWord ++ tailWord_3058190).sum := by decide
  have hdescent : baseEnd_3058190 < baseStart_3058190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058205 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3058205 : Nat := 118140960795 + 3058205 * 2 ^ 59
def prefixEnd_3058205 : Nat := 4983230072969 + 3 ^ 40 * 3058205 * 2
def baseEnd_3058205 : Nat := 523443034994437497524359

theorem tailTrace_3058205 : CollatzResearch.WordTrace tailWord_3058205 prefixEnd_3058205 523443034994437497524359 := by
  unfold tailWord_3058205
  simp only [CollatzResearch.WordTrace]
  refine ⟨111541899885653059676696069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74361266590435373117797379 111541899885653059676696069)
  ·
    refine ⟨20914106228559948689380513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111541899885653059676696069 20914106228559948689380513)
    ·
      refine ⟨15685579671419961517035385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20914106228559948689380513 15685579671419961517035385)
      ·
        refine ⟨11764184753564971137776539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685579671419961517035385 11764184753564971137776539)
        ·
          refine ⟨17646277130347456706664809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764184753564971137776539 17646277130347456706664809)
          ·
            refine ⟨13234707847760592529998607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17646277130347456706664809 13234707847760592529998607)
            ·
              refine ⟨19852061771640888794997911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13234707847760592529998607 19852061771640888794997911)
              ·
                refine ⟨29778092657461333192496867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19852061771640888794997911 29778092657461333192496867)
                ·
                  refine ⟨44667138986191999788745301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29778092657461333192496867 44667138986191999788745301)
                  ·
                    refine ⟨523443034994437497524359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44667138986191999788745301 523443034994437497524359)
                    ·
                      rfl

theorem cell23_3058205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3058205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058205 prefixEnd_3058205 := by exact prefixLift 3058205
  have htrace : WordTrace (prefixWord ++ tailWord_3058205) baseStart_3058205 baseEnd_3058205 := by
    simpa [prefixWord, tailWord_3058205, baseEnd_3058205] using wordTrace_append hprefix tailTrace_3058205
  have hstable : (prefixWord ++ tailWord_3058205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058205).length < 2 ^ (prefixWord ++ tailWord_3058205).sum := by decide
  have hdescent : baseEnd_3058205 < baseStart_3058205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058229 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_3058229 : Nat := 118140960795 + 3058229 * 2 ^ 59
def prefixEnd_3058229 : Nat := 4983230072969 + 3 ^ 40 * 3058229 * 2
def baseEnd_3058229 : Nat := 1570341428519020398672967

theorem tailTrace_3058229 : CollatzResearch.WordTrace tailWord_3058229 prefixEnd_3058229 1570341428519020398672967 := by
  unfold tailWord_3058229
  simp only [CollatzResearch.WordTrace]
  refine ⟨111542775237566111775569741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74361850158377407850379827 111542775237566111775569741)
  ·
    refine ⟨41828540714087291915838653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111542775237566111775569741 41828540714087291915838653)
    ·
      refine ⟨15685702767782734468439495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41828540714087291915838653 15685702767782734468439495)
      ·
        refine ⟨23528554151674101702659243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15685702767782734468439495 23528554151674101702659243)
        ·
          refine ⟨35292831227511152553988865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23528554151674101702659243 35292831227511152553988865)
          ·
            refine ⟨26469623420633364415491649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35292831227511152553988865 26469623420633364415491649)
            ·
              refine ⟨19852217565475023311618737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26469623420633364415491649 19852217565475023311618737)
              ·
                refine ⟨14889163174106267483714053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19852217565475023311618737 14889163174106267483714053)
                ·
                  refine ⟨2791718095144925153196385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14889163174106267483714053 2791718095144925153196385)
                  ·
                    refine ⟨2093788571358693864897289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791718095144925153196385 2093788571358693864897289)
                    ·
                      refine ⟨1570341428519020398672967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093788571358693864897289 1570341428519020398672967)
                      ·
                        rfl

theorem cell23_3058229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_3058229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058229 prefixEnd_3058229 := by exact prefixLift 3058229
  have htrace : WordTrace (prefixWord ++ tailWord_3058229) baseStart_3058229 baseEnd_3058229 := by
    simpa [prefixWord, tailWord_3058229, baseEnd_3058229] using wordTrace_append hprefix tailTrace_3058229
  have hstable : (prefixWord ++ tailWord_3058229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058229).length < 2 ^ (prefixWord ++ tailWord_3058229).sum := by decide
  have hdescent : baseEnd_3058229 < baseStart_3058229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058252 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 5]
def baseStart_3058252 : Nat := 118140960795 + 3058252 * 2 ^ 59
def prefixEnd_3058252 : Nat := 4983230072969 + 3 ^ 40 * 3058252 * 2
def baseEnd_3058252 : Nat := 174483693174897089853929

theorem tailTrace_3058252 : CollatzResearch.WordTrace tailWord_3058252 prefixEnd_3058252 174483693174897089853929 := by
  unfold tailWord_3058252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55771807058241393351828505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74362409410988524469104673 55771807058241393351828505)
  ·
    refine ⟨41828855293681045013871379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55771807058241393351828505 41828855293681045013871379)
    ·
      refine ⟨62743282940521567520807069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41828855293681045013871379 62743282940521567520807069)
      ·
        refine ⟨23528731102695587820302651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62743282940521567520807069 23528731102695587820302651)
        ·
          refine ⟨35293096654043381730453977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23528731102695587820302651 35293096654043381730453977)
          ·
            refine ⟨26469822490532536297840483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35293096654043381730453977 26469822490532536297840483)
            ·
              refine ⟨39704733735798804446760725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26469822490532536297840483 39704733735798804446760725)
              ·
                refine ⟨1861159393865568958441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39704733735798804446760725 1861159393865568958441909)
                ·
                  refine ⟨174483693174897089853929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861159393865568958441909 174483693174897089853929)
                  ·
                    rfl

theorem cell23_3058252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_3058252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058252 prefixEnd_3058252 := by exact prefixLift 3058252
  have htrace : WordTrace (prefixWord ++ tailWord_3058252) baseStart_3058252 baseEnd_3058252 := by
    simpa [prefixWord, tailWord_3058252, baseEnd_3058252] using wordTrace_append hprefix tailTrace_3058252
  have hstable : (prefixWord ++ tailWord_3058252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058252).length < 2 ^ (prefixWord ++ tailWord_3058252).sum := by decide
  have hdescent : baseEnd_3058252 < baseStart_3058252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058272 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2]
def baseStart_3058272 : Nat := 118140960795 + 3058272 * 2 ^ 59
def prefixEnd_3058272 : Nat := 4983230072969 + 3 ^ 40 * 3058272 * 2
def baseEnd_3058272 : Nat := 1570363508187163730435269

theorem tailTrace_3058272 : CollatzResearch.WordTrace tailWord_3058272 prefixEnd_3058272 1570363508187163730435269 := by
  unfold tailWord_3058272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55772171788205165059692535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74362895717606886746256713 55772171788205165059692535)
  ·
    refine ⟨83658257682307747589538803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55772171788205165059692535 83658257682307747589538803)
    ·
      refine ⟨125487386523461621384308205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83658257682307747589538803 125487386523461621384308205)
      ·
        refine ⟨47057769946298108019115577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125487386523461621384308205 47057769946298108019115577)
        ·
          refine ⟨35293327459723581014336683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47057769946298108019115577 35293327459723581014336683)
          ·
            refine ⟨52939991189585371521505025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35293327459723581014336683 52939991189585371521505025)
            ·
              refine ⟨39704993392189028641128769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52939991189585371521505025 39704993392189028641128769)
              ·
                refine ⟨29778745044141771480846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39704993392189028641128769 29778745044141771480846577)
                ·
                  refine ⟨22334058783106328610634933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29778745044141771480846577 22334058783106328610634933)
                  ·
                    refine ⟨2093818010916218307247025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22334058783106328610634933 2093818010916218307247025)
                    ·
                      refine ⟨1570363508187163730435269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093818010916218307247025 1570363508187163730435269)
                      ·
                        rfl

theorem cell23_3058272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_3058272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058272 prefixEnd_3058272 := by exact prefixLift 3058272
  have htrace : WordTrace (prefixWord ++ tailWord_3058272) baseStart_3058272 baseEnd_3058272 := by
    simpa [prefixWord, tailWord_3058272, baseEnd_3058272] using wordTrace_append hprefix tailTrace_3058272
  have hstable : (prefixWord ++ tailWord_3058272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058272).length < 2 ^ (prefixWord ++ tailWord_3058272).sum := by decide
  have hdescent : baseEnd_3058272 < baseStart_3058272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058282 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3058282 : Nat := 118140960795 + 3058282 * 2 ^ 59
def prefixEnd_3058282 : Nat := 4983230072969 + 3 ^ 40 * 3058282 * 2
def baseEnd_3058282 : Nat := 523456214331236230436741

theorem tailTrace_3058282 : CollatzResearch.WordTrace tailWord_3058282 prefixEnd_3058282 523456214331236230436741 := by
  unfold tailWord_3058282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27886177076593525456812275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74363138870916067884832733 27886177076593525456812275)
  ·
    refine ⟨41829265614890288185218413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27886177076593525456812275 41829265614890288185218413)
    ·
      refine ⟨15685974605583858069456905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41829265614890288185218413 15685974605583858069456905)
      ·
        refine ⟨11764480954187893552092679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685974605583858069456905 11764480954187893552092679)
        ·
          refine ⟨17646721431281840328139019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764480954187893552092679 17646721431281840328139019)
          ·
            refine ⟨26470082146922760492208529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17646721431281840328139019 26470082146922760492208529)
            ·
              refine ⟨19852561610192070369156397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26470082146922760492208529 19852561610192070369156397)
              ·
                refine ⟨7444710603822026388433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19852561610192070369156397 7444710603822026388433649)
                ·
                  refine ⟨5583532952866519791325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7444710603822026388433649 5583532952866519791325237)
                  ·
                    refine ⟨523456214331236230436741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5583532952866519791325237 523456214331236230436741)
                    ·
                      rfl

theorem cell23_3058282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3058282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058282 prefixEnd_3058282 := by exact prefixLift 3058282
  have htrace : WordTrace (prefixWord ++ tailWord_3058282) baseStart_3058282 baseEnd_3058282 := by
    simpa [prefixWord, tailWord_3058282, baseEnd_3058282] using wordTrace_append hprefix tailTrace_3058282
  have hstable : (prefixWord ++ tailWord_3058282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058282).length < 2 ^ (prefixWord ++ tailWord_3058282).sum := by decide
  have hdescent : baseEnd_3058282 < baseStart_3058282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058286 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_3058286 : Nat := 118140960795 + 3058286 * 2 ^ 59
def prefixEnd_3058286 : Nat := 4983230072969 + 3 ^ 40 * 3058286 * 2
def baseEnd_3058286 : Nat := 174485632990702963962245

theorem tailTrace_3058286 : CollatzResearch.WordTrace tailWord_3058286 prefixEnd_3058286 174485632990702963962245 := by
  unfold tailWord_3058286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943106774794951313799339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74363236132239740340263141 13943106774794951313799339)
  ·
    refine ⟨20914660162192426970699009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13943106774794951313799339 20914660162192426970699009)
    ·
      refine ⟨15685995121644320228024257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20914660162192426970699009 15685995121644320228024257)
      ·
        refine ⟨11764496341233240171018193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685995121644320228024257 11764496341233240171018193)
        ·
          refine ⟨8823372255924930128263645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11764496341233240171018193 8823372255924930128263645)
          ·
            refine ⟨3308764595971848798098867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8823372255924930128263645 3308764595971848798098867)
            ·
              refine ⟨4963146893957773197148301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308764595971848798098867 4963146893957773197148301)
              ·
                refine ⟨1861180085234164948930613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4963146893957773197148301 1861180085234164948930613)
                ·
                  refine ⟨174485632990702963962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861180085234164948930613 174485632990702963962245)
                  ·
                    rfl

theorem cell23_3058286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_3058286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058286 prefixEnd_3058286 := by exact prefixLift 3058286
  have htrace : WordTrace (prefixWord ++ tailWord_3058286) baseStart_3058286 baseEnd_3058286 := by
    simpa [prefixWord, tailWord_3058286, baseEnd_3058286] using wordTrace_append hprefix tailTrace_3058286
  have hstable : (prefixWord ++ tailWord_3058286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058286).length < 2 ^ (prefixWord ++ tailWord_3058286).sum := by decide
  have hdescent : baseEnd_3058286 < baseStart_3058286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058315 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_3058315 : Nat := 118140960795 + 3058315 * 2 ^ 59
def prefixEnd_3058315 : Nat := 4983230072969 + 3 ^ 40 * 3058315 * 2
def baseEnd_3058315 : Nat := 1570385587855307062197571

theorem tailTrace_3058315 : CollatzResearch.WordTrace tailWord_3058315 prefixEnd_3058315 1570385587855307062197571 := by
  unfold tailWord_3058315
  simp only [CollatzResearch.WordTrace]
  refine ⟨111545911915254548463200399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74363941276836365642133599 111545911915254548463200399)
  ·
    refine ⟨167318867872881822694800599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111545911915254548463200399 167318867872881822694800599)
    ·
      refine ⟨250978301809322734042200899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167318867872881822694800599 250978301809322734042200899)
      ·
        refine ⟨376467452713984101063301349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250978301809322734042200899 376467452713984101063301349)
        ·
          refine ⟨70587647383872018949369003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376467452713984101063301349 70587647383872018949369003)
          ·
            refine ⟨105881471075808028424053505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70587647383872018949369003 105881471075808028424053505)
            ·
              refine ⟨79411103306856021318040129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105881471075808028424053505 79411103306856021318040129)
              ·
                refine ⟨59558327480142015988530097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79411103306856021318040129 59558327480142015988530097)
                ·
                  refine ⟨44668745610106511991397573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59558327480142015988530097 44668745610106511991397573)
                  ·
                    refine ⟨8375389801894970998387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44668745610106511991397573 8375389801894970998387045)
                    ·
                      refine ⟨1570385587855307062197571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8375389801894970998387045 1570385587855307062197571)
                      ·
                        rfl

theorem cell23_3058315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_3058315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058315 prefixEnd_3058315 := by exact prefixLift 3058315
  have htrace : WordTrace (prefixWord ++ tailWord_3058315) baseStart_3058315 baseEnd_3058315 := by
    simpa [prefixWord, tailWord_3058315, baseEnd_3058315] using wordTrace_append hprefix tailTrace_3058315
  have hstable : (prefixWord ++ tailWord_3058315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058315).length < 2 ^ (prefixWord ++ tailWord_3058315).sum := by decide
  have hdescent : baseEnd_3058315 < baseStart_3058315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058359 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 6]
def baseStart_3058359 : Nat := 118140960795 + 3058359 * 2 ^ 59
def prefixEnd_3058359 : Nat := 4983230072969 + 3 ^ 40 * 3058359 * 2
def baseEnd_3058359 : Nat := 174489797889344987783041

theorem tailTrace_3058359 : CollatzResearch.WordTrace tailWord_3058359 prefixEnd_3058359 174489797889344987783041 := by
  unfold tailWord_3058359
  simp only [CollatzResearch.WordTrace]
  refine ⟨111547516727095143977802131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74365011151396762651868087 111547516727095143977802131)
  ·
    refine ⟨167321275090642715966703197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111547516727095143977802131 167321275090642715966703197)
    ·
      refine ⟨62745478158991018487513699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167321275090642715966703197 62745478158991018487513699)
      ·
        refine ⟨94118217238486527731270549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62745478158991018487513699 94118217238486527731270549)
        ·
          refine ⟨4411791433054055987403307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94118217238486527731270549 4411791433054055987403307)
          ·
            refine ⟨6617687149581083981104961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411791433054055987403307 6617687149581083981104961)
            ·
              refine ⟨4963265362185812985828721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6617687149581083981104961 4963265362185812985828721)
              ·
                refine ⟨3722449021639359739371541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963265362185812985828721 3722449021639359739371541)
                ·
                  refine ⟨174489797889344987783041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3722449021639359739371541 174489797889344987783041)
                  ·
                    rfl

theorem cell23_3058359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 6].length) (baseStart_3058359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058359 prefixEnd_3058359 := by exact prefixLift 3058359
  have htrace : WordTrace (prefixWord ++ tailWord_3058359) baseStart_3058359 baseEnd_3058359 := by
    simpa [prefixWord, tailWord_3058359, baseEnd_3058359] using wordTrace_append hprefix tailTrace_3058359
  have hstable : (prefixWord ++ tailWord_3058359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058359).length < 2 ^ (prefixWord ++ tailWord_3058359).sum := by decide
  have hdescent : baseEnd_3058359 < baseStart_3058359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058403 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3058403 : Nat := 118140960795 + 3058403 * 2 ^ 59
def prefixEnd_3058403 : Nat := 4983230072969 + 3 ^ 40 * 3058403 * 2
def baseEnd_3058403 : Nat := 1570430774152902717897167

theorem tailTrace_3058403 : CollatzResearch.WordTrace tailWord_3058403 prefixEnd_3058403 1570430774152902717897167 := by
  unfold tailWord_3058403
  simp only [CollatzResearch.WordTrace]
  refine ⟨111549121538935739492403863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74366081025957159661602575 111549121538935739492403863)
  ·
    refine ⟨167323682308403609238605795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111549121538935739492403863 167323682308403609238605795)
    ·
      refine ⟨250985523462605413857908693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167323682308403609238605795 250985523462605413857908693)
      ·
        refine ⟨5882473206154814387294735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 250985523462605413857908693 5882473206154814387294735)
        ·
          refine ⟨8823709809232221580942103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882473206154814387294735 8823709809232221580942103)
          ·
            refine ⟨13235564713848332371413155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823709809232221580942103 13235564713848332371413155)
            ·
              refine ⟨19853347070772498557119733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13235564713848332371413155 19853347070772498557119733)
              ·
                refine ⟨1861251287884921739729975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19853347070772498557119733 1861251287884921739729975)
                ·
                  refine ⟨2791876931827382609594963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861251287884921739729975 2791876931827382609594963)
                  ·
                    refine ⟨4187815397741073914392445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2791876931827382609594963 4187815397741073914392445)
                    ·
                      refine ⟨1570430774152902717897167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187815397741073914392445 1570430774152902717897167)
                      ·
                        rfl

theorem cell23_3058403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3058403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058403 prefixEnd_3058403 := by exact prefixLift 3058403
  have htrace : WordTrace (prefixWord ++ tailWord_3058403) baseStart_3058403 baseEnd_3058403 := by
    simpa [prefixWord, tailWord_3058403, baseEnd_3058403] using wordTrace_append hprefix tailTrace_3058403
  have hstable : (prefixWord ++ tailWord_3058403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058403).length < 2 ^ (prefixWord ++ tailWord_3058403).sum := by decide
  have hdescent : baseEnd_3058403 < baseStart_3058403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058412 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3058412 : Nat := 118140960795 + 3058412 * 2 ^ 59
def prefixEnd_3058412 : Nat := 4983230072969 + 3 ^ 40 * 3058412 * 2
def baseEnd_3058412 : Nat := 1570435395478793182684625

theorem tailTrace_3058412 : CollatzResearch.WordTrace tailWord_3058412 prefixEnd_3058412 1570435395478793182684625 := by
  unfold tailWord_3058412
  simp only [CollatzResearch.WordTrace]
  refine ⟨55774724897951567014740745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74366299863935422686320993 55774724897951567014740745)
  ·
    refine ⟨41831043673463675261055559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55774724897951567014740745 41831043673463675261055559)
    ·
      refine ⟨62746565510195512891583339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41831043673463675261055559 62746565510195512891583339)
      ·
        refine ⟨94119848265293269337375009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62746565510195512891583339 94119848265293269337375009)
        ·
          refine ⟨70589886198969952003031257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94119848265293269337375009 70589886198969952003031257)
          ·
            refine ⟨52942414649227464002273443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70589886198969952003031257 52942414649227464002273443)
            ·
              refine ⟨79413621973841196003410165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52942414649227464002273443 79413621973841196003410165)
              ·
                refine ⟨7445027060047612125319703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79413621973841196003410165 7445027060047612125319703)
                ·
                  refine ⟨11167540590071418187979555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445027060047612125319703 11167540590071418187979555)
                  ·
                    refine ⟨16751310885107127281969333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11167540590071418187979555 16751310885107127281969333)
                    ·
                      refine ⟨1570435395478793182684625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16751310885107127281969333 1570435395478793182684625)
                      ·
                        rfl

theorem cell23_3058412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3058412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058412 prefixEnd_3058412 := by exact prefixLift 3058412
  have htrace : WordTrace (prefixWord ++ tailWord_3058412) baseStart_3058412 baseEnd_3058412 := by
    simpa [prefixWord, tailWord_3058412, baseEnd_3058412] using wordTrace_append hprefix tailTrace_3058412
  have hstable : (prefixWord ++ tailWord_3058412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058412).length < 2 ^ (prefixWord ++ tailWord_3058412).sum := by decide
  have hdescent : baseEnd_3058412 < baseStart_3058412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058426 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_3058426 : Nat := 118140960795 + 3058426 * 2 ^ 59
def prefixEnd_3058426 : Nat := 4983230072969 + 3 ^ 40 * 3058426 * 2
def baseEnd_3058426 : Nat := 1570442584207956127909561

theorem tailTrace_3058426 : CollatzResearch.WordTrace tailWord_3058426 prefixEnd_3058426 1570442584207956127909561 := by
  unfold tailWord_3058426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887490104463103605122783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74366640278568276280327421 27887490104463103605122783)
  ·
    refine ⟨41831235156694655407684175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27887490104463103605122783 41831235156694655407684175)
    ·
      refine ⟨62746852735041983111526263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41831235156694655407684175 62746852735041983111526263)
      ·
        refine ⟨94120279102562974667289395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62746852735041983111526263 94120279102562974667289395)
        ·
          refine ⟨141180418653844462000934093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94120279102562974667289395 141180418653844462000934093)
          ·
            refine ⟨52942656995191673250350285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141180418653844462000934093 52942656995191673250350285)
            ·
              refine ⟨19853496373196877468881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52942656995191673250350285 19853496373196877468881357)
              ·
                refine ⟨7445061139948829050830509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19853496373196877468881357 7445061139948829050830509)
                ·
                  refine ⟨2791897927480810894061441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7445061139948829050830509 2791897927480810894061441)
                  ·
                    refine ⟨2093923445610608170546081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791897927480810894061441 2093923445610608170546081)
                    ·
                      refine ⟨1570442584207956127909561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093923445610608170546081 1570442584207956127909561)
                      ·
                        rfl

theorem cell23_3058426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_3058426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058426 prefixEnd_3058426 := by exact prefixLift 3058426
  have htrace : WordTrace (prefixWord ++ tailWord_3058426) baseStart_3058426 baseEnd_3058426 := by
    simpa [prefixWord, tailWord_3058426, baseEnd_3058426] using wordTrace_append hprefix tailTrace_3058426
  have hstable : (prefixWord ++ tailWord_3058426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058426).length < 2 ^ (prefixWord ++ tailWord_3058426).sum := by decide
  have hdescent : baseEnd_3058426 < baseStart_3058426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058439 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3058439 : Nat := 118140960795 + 3058439 * 2 ^ 59
def prefixEnd_3058439 : Nat := 4983230072969 + 3 ^ 40 * 3058439 * 2
def baseEnd_3058439 : Nat := 1570449259456464577047001

theorem tailTrace_3058439 : CollatzResearch.WordTrace tailWord_3058439 prefixEnd_3058439 1570449259456464577047001 := by
  unfold tailWord_3058439
  simp only [CollatzResearch.WordTrace]
  refine ⟨111550434566805317640714371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74366956377870211760476247 111550434566805317640714371)
  ·
    refine ⟨167325651850207976461071557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111550434566805317640714371 167325651850207976461071557)
    ·
      refine ⟨31373559721913995586450917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167325651850207976461071557 31373559721913995586450917)
      ·
        refine ⟨5882542447858874172459547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31373559721913995586450917 5882542447858874172459547)
        ·
          refine ⟨8823813671788311258689321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882542447858874172459547 8823813671788311258689321)
          ·
            refine ⟨6617860253841233444016991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8823813671788311258689321 6617860253841233444016991)
            ·
              refine ⟨9926790380761850166025487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617860253841233444016991 9926790380761850166025487)
              ·
                refine ⟨14890185571142775249038231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9926790380761850166025487 14890185571142775249038231)
                ·
                  refine ⟨22335278356714162873557347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14890185571142775249038231 22335278356714162873557347)
                  ·
                    refine ⟨33502917535071244310336021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22335278356714162873557347 33502917535071244310336021)
                    ·
                      refine ⟨1570449259456464577047001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33502917535071244310336021 1570449259456464577047001)
                      ·
                        rfl

theorem cell23_3058439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3058439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058439 prefixEnd_3058439 := by exact prefixLift 3058439
  have htrace : WordTrace (prefixWord ++ tailWord_3058439) baseStart_3058439 baseEnd_3058439 := by
    simpa [prefixWord, tailWord_3058439, baseEnd_3058439] using wordTrace_append hprefix tailTrace_3058439
  have hstable : (prefixWord ++ tailWord_3058439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058439).length < 2 ^ (prefixWord ++ tailWord_3058439).sum := by decide
  have hdescent : baseEnd_3058439 < baseStart_3058439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058460 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3058460 : Nat := 118140960795 + 3058460 * 2 ^ 59
def prefixEnd_3058460 : Nat := 4983230072969 + 3 ^ 40 * 3058460 * 2
def baseEnd_3058460 : Nat := 1570460042550208994884405

theorem tailTrace_3058460 : CollatzResearch.WordTrace tailWord_3058460 prefixEnd_3058460 1570460042550208994884405 := by
  unfold tailWord_3058460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55775600249864619113614417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74367466999819492151485889 55775600249864619113614417)
  ·
    refine ⟨41831700187398464335210813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55775600249864619113614417 41831700187398464335210813)
    ·
      refine ⟨15686887570274424125704055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41831700187398464335210813 15686887570274424125704055)
      ·
        refine ⟨23530331355411636188556083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15686887570274424125704055 23530331355411636188556083)
        ·
          refine ⟨35295497033117454282834125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23530331355411636188556083 35295497033117454282834125)
          ·
            refine ⟨13235811387419045356062797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35295497033117454282834125 13235811387419045356062797)
            ·
              refine ⟨4963429270282142008523549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235811387419045356062797 4963429270282142008523549)
              ·
                refine ⟨1861285976355803253196331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4963429270282142008523549 1861285976355803253196331)
                ·
                  refine ⟨2791928964533704879794497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861285976355803253196331 2791928964533704879794497)
                  ·
                    refine ⟨2093946723400278659845873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791928964533704879794497 2093946723400278659845873)
                    ·
                      refine ⟨1570460042550208994884405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093946723400278659845873 1570460042550208994884405)
                      ·
                        rfl

theorem cell23_3058460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3058460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058460 prefixEnd_3058460 := by exact prefixLift 3058460
  have htrace : WordTrace (prefixWord ++ tailWord_3058460) baseStart_3058460 baseEnd_3058460 := by
    simpa [prefixWord, tailWord_3058460, baseEnd_3058460] using wordTrace_append hprefix tailTrace_3058460
  have hstable : (prefixWord ++ tailWord_3058460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058460).length < 2 ^ (prefixWord ++ tailWord_3058460).sum := by decide
  have hdescent : baseEnd_3058460 < baseStart_3058460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058476 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_3058476 : Nat := 118140960795 + 3058476 * 2 ^ 59
def prefixEnd_3058476 : Nat := 4983230072969 + 3 ^ 40 * 3058476 * 2
def baseEnd_3058476 : Nat := 1570468258240680932284331

theorem tailTrace_3058476 : CollatzResearch.WordTrace tailWord_3058476 prefixEnd_3058476 1570468258240680932284331 := by
  unfold tailWord_3058476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55775892033835636479905641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74367856045114181973207521 55775892033835636479905641)
  ·
    refine ⟨41831919025376727359929231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55775892033835636479905641 41831919025376727359929231)
    ·
      refine ⟨62747878538065091039893847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41831919025376727359929231 62747878538065091039893847)
      ·
        refine ⟨94121817807097636559840771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62747878538065091039893847 94121817807097636559840771)
        ·
          refine ⟨141182726710646454839761157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94121817807097636559840771 141182726710646454839761157)
          ·
            refine ⟨26471761258246210282455217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141182726710646454839761157 26471761258246210282455217)
            ·
              refine ⟨19853820943684657711841413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26471761258246210282455217 19853820943684657711841413)
              ·
                refine ⟨3722591426940873320970265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19853820943684657711841413 3722591426940873320970265)
                ·
                  refine ⟨2791943570205654990727699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722591426940873320970265 2791943570205654990727699)
                  ·
                    refine ⟨4187915355308482486091549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2791943570205654990727699 4187915355308482486091549)
                    ·
                      refine ⟨1570468258240680932284331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187915355308482486091549 1570468258240680932284331)
                      ·
                        rfl

theorem cell23_3058476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_3058476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058476 prefixEnd_3058476 := by exact prefixLift 3058476
  have htrace : WordTrace (prefixWord ++ tailWord_3058476) baseStart_3058476 baseEnd_3058476 := by
    simpa [prefixWord, tailWord_3058476, baseEnd_3058476] using wordTrace_append hprefix tailTrace_3058476
  have hstable : (prefixWord ++ tailWord_3058476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058476).length < 2 ^ (prefixWord ++ tailWord_3058476).sum := by decide
  have hdescent : baseEnd_3058476 < baseStart_3058476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058492 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3058492 : Nat := 118140960795 + 3058492 * 2 ^ 59
def prefixEnd_3058492 : Nat := 4983230072969 + 3 ^ 40 * 3058492 * 2
def baseEnd_3058492 : Nat := 523492157977050956561419

theorem tailTrace_3058492 : CollatzResearch.WordTrace tailWord_3058492 prefixEnd_3058492 523492157977050956561419 := by
  unfold tailWord_3058492
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776183817806653846196865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74368245090408871794929153 55776183817806653846196865)
  ·
    refine ⟨41832137863354990384647649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55776183817806653846196865 41832137863354990384647649)
    ·
      refine ⟨31374103397516242788485737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41832137863354990384647649 31374103397516242788485737)
      ·
        refine ⟨23530577548137182091364303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31374103397516242788485737 23530577548137182091364303)
        ·
          refine ⟨35295866322205773137046455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23530577548137182091364303 35295866322205773137046455)
          ·
            refine ⟨52943799483308659705569683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35295866322205773137046455 52943799483308659705569683)
            ·
              refine ⟨79415699224962989558354525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52943799483308659705569683 79415699224962989558354525)
              ·
                refine ⟨29780887209361121084382947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79415699224962989558354525 29780887209361121084382947)
                ·
                  refine ⟨44671330814041681626574421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29780887209361121084382947 44671330814041681626574421)
                  ·
                    refine ⟨523492157977050956561419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44671330814041681626574421 523492157977050956561419)
                    ·
                      rfl

theorem cell23_3058492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3058492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058492 prefixEnd_3058492 := by exact prefixLift 3058492
  have htrace : WordTrace (prefixWord ++ tailWord_3058492) baseStart_3058492 baseEnd_3058492 := by
    simpa [prefixWord, tailWord_3058492, baseEnd_3058492] using wordTrace_append hprefix tailTrace_3058492
  have hstable : (prefixWord ++ tailWord_3058492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058492).length < 2 ^ (prefixWord ++ tailWord_3058492).sum := by decide
  have hdescent : baseEnd_3058492 < baseStart_3058492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058497 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3058497 : Nat := 118140960795 + 3058497 * 2 ^ 59
def prefixEnd_3058497 : Nat := 4983230072969 + 3 ^ 40 * 3058497 * 2
def baseEnd_3058497 : Nat := 1570479041334425350121735

theorem tailTrace_3058497 : CollatzResearch.WordTrace tailWord_3058497 prefixEnd_3058497 1570479041334425350121735 := by
  unfold tailWord_3058497
  simp only [CollatzResearch.WordTrace]
  refine ⟨111552550000595193546325745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74368366667063462364217163 111552550000595193546325745)
  ·
    refine ⟨83664412500446395159744309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111552550000595193546325745 83664412500446395159744309)
    ·
      refine ⟨7843538671916849546226029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83664412500446395159744309 7843538671916849546226029)
      ·
        refine ⟨2941327001968818579834761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7843538671916849546226029 2941327001968818579834761)
        ·
          refine ⟨2205995251476613934876071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941327001968818579834761 2205995251476613934876071)
          ·
            refine ⟨3308992877214920902314107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205995251476613934876071 3308992877214920902314107)
            ·
              refine ⟨4963489315822381353471161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308992877214920902314107 4963489315822381353471161)
              ·
                refine ⟨3722616986866786015103371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963489315822381353471161 3722616986866786015103371)
                ·
                  refine ⟨5583925480300179022655057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722616986866786015103371 5583925480300179022655057)
                  ·
                    refine ⟨4187944110225134266991293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5583925480300179022655057 4187944110225134266991293)
                    ·
                      refine ⟨1570479041334425350121735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4187944110225134266991293 1570479041334425350121735)
                      ·
                        rfl

theorem cell23_3058497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3058497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058497 prefixEnd_3058497 := by exact prefixLift 3058497
  have htrace : WordTrace (prefixWord ++ tailWord_3058497) baseStart_3058497 baseEnd_3058497 := by
    simpa [prefixWord, tailWord_3058497, baseEnd_3058497] using wordTrace_append hprefix tailTrace_3058497
  have hstable : (prefixWord ++ tailWord_3058497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058497).length < 2 ^ (prefixWord ++ tailWord_3058497).sum := by decide
  have hdescent : baseEnd_3058497 < baseStart_3058497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058519 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3058519 : Nat := 118140960795 + 3058519 * 2 ^ 59
def prefixEnd_3058519 : Nat := 4983230072969 + 3 ^ 40 * 3058519 * 2
def baseEnd_3058519 : Nat := 1570490337908824264046633

theorem tailTrace_3058519 : CollatzResearch.WordTrace tailWord_3058519 prefixEnd_3058519 1570490337908824264046633 := by
  unfold tailWord_3058519
  simp only [CollatzResearch.WordTrace]
  refine ⟨111553352406515491303626611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74368901604343660869084407 111553352406515491303626611)
  ·
    refine ⟨167330028609773236955439917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111553352406515491303626611 167330028609773236955439917)
    ·
      refine ⟨62748760728664963858289969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167330028609773236955439917 62748760728664963858289969)
      ·
        refine ⟨47061570546498722893717477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62748760728664963858289969 47061570546498722893717477)
        ·
          refine ⟨8824044477468510542572027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47061570546498722893717477 8824044477468510542572027)
          ·
            refine ⟨13236066716202765813858041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824044477468510542572027 13236066716202765813858041)
            ·
              refine ⟨9927050037152074360393531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236066716202765813858041 9927050037152074360393531)
              ·
                refine ⟨14890575055728111540590297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927050037152074360393531 14890575055728111540590297)
                ·
                  refine ⟨11167931291796083655442723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14890575055728111540590297 11167931291796083655442723)
                  ·
                    refine ⟨16751896937694125483164085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11167931291796083655442723 16751896937694125483164085)
                    ·
                      refine ⟨1570490337908824264046633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16751896937694125483164085 1570490337908824264046633)
                      ·
                        rfl

theorem cell23_3058519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3058519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058519 prefixEnd_3058519 := by exact prefixLift 3058519
  have htrace : WordTrace (prefixWord ++ tailWord_3058519) baseStart_3058519 baseEnd_3058519 := by
    simpa [prefixWord, tailWord_3058519, baseEnd_3058519] using wordTrace_append hprefix tailTrace_3058519
  have hstable : (prefixWord ++ tailWord_3058519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058519).length < 2 ^ (prefixWord ++ tailWord_3058519).sum := by decide
  have hdescent : baseEnd_3058519 < baseStart_3058519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058533 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_3058533 : Nat := 118140960795 + 3058533 * 2 ^ 59
def prefixEnd_3058533 : Nat := 4983230072969 + 3 ^ 40 * 3058533 * 2
def baseEnd_3058533 : Nat := 1570497526637987209271569

theorem tailTrace_3058533 : CollatzResearch.WordTrace tailWord_3058533 prefixEnd_3058533 1570497526637987209271569 := by
  unfold tailWord_3058533
  simp only [CollatzResearch.WordTrace]
  refine ⟨111553863028464771694636253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74369242018976514463090835 111553863028464771694636253)
  ·
    refine ⟨41832698635674289385488595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111553863028464771694636253 41832698635674289385488595)
    ·
      refine ⟨62749047953511434078232893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41832698635674289385488595 62749047953511434078232893)
      ·
        refine ⟨23530892982566787779337335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62749047953511434078232893 23530892982566787779337335)
        ·
          refine ⟨35296339473850181669006003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23530892982566787779337335 35296339473850181669006003)
          ·
            refine ⟨52944509210775272503509005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35296339473850181669006003 52944509210775272503509005)
            ·
              refine ⟨19854190954040727188815877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52944509210775272503509005 19854190954040727188815877)
              ·
                refine ⟨3722660803882636347902977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19854190954040727188815877 3722660803882636347902977)
                ·
                  refine ⟨2791995602911977260927233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722660803882636347902977 2791995602911977260927233)
                  ·
                    refine ⟨2093996702183982945695425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791995602911977260927233 2093996702183982945695425)
                    ·
                      refine ⟨1570497526637987209271569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093996702183982945695425 1570497526637987209271569)
                      ·
                        rfl

theorem cell23_3058533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_3058533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058533 prefixEnd_3058533 := by exact prefixLift 3058533
  have htrace : WordTrace (prefixWord ++ tailWord_3058533) baseStart_3058533 baseEnd_3058533 := by
    simpa [prefixWord, tailWord_3058533, baseEnd_3058533] using wordTrace_append hprefix tailTrace_3058533
  have hstable : (prefixWord ++ tailWord_3058533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058533).length < 2 ^ (prefixWord ++ tailWord_3058533).sum := by decide
  have hdescent : baseEnd_3058533 < baseStart_3058533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058550 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3058550 : Nat := 118140960795 + 3058550 * 2 ^ 59
def prefixEnd_3058550 : Nat := 4983230072969 + 3 ^ 40 * 3058550 * 2
def baseEnd_3058550 : Nat := 1570506255809113642758991

theorem tailTrace_3058550 : CollatzResearch.WordTrace tailWord_3058550 prefixEnd_3058550 1570506255809113642758991 := by
  unfold tailWord_3058550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972155191837698974875319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74369655379602122398670069 6972155191837698974875319)
  ·
    refine ⟨10458232787756548462312979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6972155191837698974875319 10458232787756548462312979)
    ·
      refine ⟨15687349181634822693469469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10458232787756548462312979 15687349181634822693469469)
      ·
        refine ⟨5882755943113058510051051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15687349181634822693469469 5882755943113058510051051)
        ·
          refine ⟨8824133914669587765076577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882755943113058510051051 8824133914669587765076577)
          ·
            refine ⟨6618100436002190823807433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824133914669587765076577 6618100436002190823807433)
            ·
              refine ⟨4963575327001643117855575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618100436002190823807433 4963575327001643117855575)
              ·
                refine ⟨7445362990502464676783363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963575327001643117855575 7445362990502464676783363)
                ·
                  refine ⟨11168044485753697015175045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445362990502464676783363 11168044485753697015175045)
                  ·
                    refine ⟨2094008341078818190345321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11168044485753697015175045 2094008341078818190345321)
                    ·
                      refine ⟨1570506255809113642758991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094008341078818190345321 1570506255809113642758991)
                      ·
                        rfl

theorem cell23_3058550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3058550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058550 prefixEnd_3058550 := by exact prefixLift 3058550
  have htrace : WordTrace (prefixWord ++ tailWord_3058550) baseStart_3058550 baseEnd_3058550 := by
    simpa [prefixWord, tailWord_3058550, baseEnd_3058550] using wordTrace_append hprefix tailTrace_3058550
  have hstable : (prefixWord ++ tailWord_3058550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058550).length < 2 ^ (prefixWord ++ tailWord_3058550).sum := by decide
  have hdescent : baseEnd_3058550 < baseStart_3058550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058569 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_3058569 : Nat := 118140960795 + 3058569 * 2 ^ 59
def prefixEnd_3058569 : Nat := 4983230072969 + 3 ^ 40 * 3058569 * 2
def baseEnd_3058569 : Nat := 523505337313849689473801

theorem tailTrace_3058569 : CollatzResearch.WordTrace tailWord_3058569 prefixEnd_3058569 523505337313849689473801 := by
  unfold tailWord_3058569
  simp only [CollatzResearch.WordTrace]
  refine ⟨111555176056334349842946761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74370117370889566561964507 111555176056334349842946761)
  ·
    refine ⟨83666382042250762382210071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111555176056334349842946761 83666382042250762382210071)
    ·
      refine ⟨125499573063376143573315107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83666382042250762382210071 125499573063376143573315107)
      ·
        refine ⟨188249359595064215359972661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125499573063376143573315107 188249359595064215359972661)
        ·
          refine ⟨17648377462037270189997437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188249359595064215359972661 17648377462037270189997437)
          ·
            refine ⟨6618141548263976321249039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17648377462037270189997437 6618141548263976321249039)
            ·
              refine ⟨9927212322395964481873559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618141548263976321249039 9927212322395964481873559)
              ·
                refine ⟨14890818483593946722810339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927212322395964481873559 14890818483593946722810339)
                ·
                  refine ⟨22336227725390920084215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14890818483593946722810339 22336227725390920084215509)
                  ·
                    refine ⟨523505337313849689473801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22336227725390920084215509 523505337313849689473801)
                    ·
                      rfl

theorem cell23_3058569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_3058569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058569 prefixEnd_3058569 := by exact prefixLift 3058569
  have htrace : WordTrace (prefixWord ++ tailWord_3058569) baseStart_3058569 baseEnd_3058569 := by
    simpa [prefixWord, tailWord_3058569, baseEnd_3058569] using wordTrace_append hprefix tailTrace_3058569
  have hstable : (prefixWord ++ tailWord_3058569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058569).length < 2 ^ (prefixWord ++ tailWord_3058569).sum := by decide
  have hdescent : baseEnd_3058569 < baseStart_3058569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058616 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_3058616 : Nat := 118140960795 + 3058616 * 2 ^ 59
def prefixEnd_3058616 : Nat := 4983230072969 + 3 ^ 40 * 3058616 * 2
def baseEnd_3058616 : Nat := 523513381844103461511229

theorem tailTrace_3058616 : CollatzResearch.WordTrace tailWord_3058616 prefixEnd_3058616 523513381844103461511229 := by
  unfold tailWord_3058616
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778445143582038434953851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74371260191442717913271801 55778445143582038434953851)
  ·
    refine ⟨83667667715373057652430777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55778445143582038434953851 83667667715373057652430777)
    ·
      refine ⟨62750750786529793239323083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83667667715373057652430777 62750750786529793239323083)
      ·
        refine ⟨94126126179794689858984625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62750750786529793239323083 94126126179794689858984625)
        ·
          refine ⟨70594594634846017394238469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94126126179794689858984625 70594594634846017394238469)
          ·
            refine ⟨13236486494033628261419713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70594594634846017394238469 13236486494033628261419713)
            ·
              refine ⟨9927364870525221196064785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236486494033628261419713 9927364870525221196064785)
              ·
                refine ⟨7445523652893915897048589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927364870525221196064785 7445523652893915897048589)
                ·
                  refine ⟨2792071369835218461393221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7445523652893915897048589 2792071369835218461393221)
                  ·
                    refine ⟨523513381844103461511229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792071369835218461393221 523513381844103461511229)
                    ·
                      rfl

theorem cell23_3058616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_3058616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058616 prefixEnd_3058616 := by exact prefixLift 3058616
  have htrace : WordTrace (prefixWord ++ tailWord_3058616) baseStart_3058616 baseEnd_3058616 := by
    simpa [prefixWord, tailWord_3058616, baseEnd_3058616] using wordTrace_append hprefix tailTrace_3058616
  have hstable : (prefixWord ++ tailWord_3058616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058616).length < 2 ^ (prefixWord ++ tailWord_3058616).sum := by decide
  have hdescent : baseEnd_3058616 < baseStart_3058616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058637 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3058637 : Nat := 118140960795 + 3058637 * 2 ^ 59
def prefixEnd_3058637 : Nat := 4983230072969 + 3 ^ 40 * 3058637 * 2
def baseEnd_3058637 : Nat := 523516976208684934123697

theorem tailTrace_3058637 : CollatzResearch.WordTrace tailWord_3058637 prefixEnd_3058637 523516976208684934123697 := by
  unfold tailWord_3058637
  simp only [CollatzResearch.WordTrace]
  refine ⟨111557656220087997456422165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74371770813391998304281443 111557656220087997456422165)
  ·
    refine ⟨5229265135316624880769789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111557656220087997456422165 5229265135316624880769789)
    ·
      refine ⟨1960974425743734330288671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5229265135316624880769789 1960974425743734330288671)
      ·
        refine ⟨2941461638615601495433007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960974425743734330288671 2941461638615601495433007)
        ·
          refine ⟨4412192457923402243149511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941461638615601495433007 4412192457923402243149511)
          ·
            refine ⟨6618288686885103364724267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412192457923402243149511 6618288686885103364724267)
            ·
              refine ⟨9927433030327655047086401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618288686885103364724267 9927433030327655047086401)
              ·
                refine ⟨7445574772745741285314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927433030327655047086401 7445574772745741285314801)
                ·
                  refine ⟨5584181079559305963986101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445574772745741285314801 5584181079559305963986101)
                  ·
                    refine ⟨523516976208684934123697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584181079559305963986101 523516976208684934123697)
                    ·
                      rfl

theorem cell23_3058637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3058637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058637 prefixEnd_3058637 := by exact prefixLift 3058637
  have htrace : WordTrace (prefixWord ++ tailWord_3058637) baseStart_3058637 baseEnd_3058637 := by
    simpa [prefixWord, tailWord_3058637, baseEnd_3058637] using wordTrace_append hprefix tailTrace_3058637
  have hstable : (prefixWord ++ tailWord_3058637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058637).length < 2 ^ (prefixWord ++ tailWord_3058637).sum := by decide
  have hdescent : baseEnd_3058637 < baseStart_3058637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058663 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 6]
def baseStart_3058663 : Nat := 118140960795 + 3058663 * 2 ^ 59
def prefixEnd_3058663 : Nat := 4983230072969 + 3 ^ 40 * 3058663 * 2
def baseEnd_3058663 : Nat := 174507142124785744516219

theorem tailTrace_3058663 : CollatzResearch.WordTrace tailWord_3058663 prefixEnd_3058663 174507142124785744516219 := by
  unfold tailWord_3058663
  simp only [CollatzResearch.WordTrace]
  refine ⟨111558604517993803896868643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74372403011995869264579095 111558604517993803896868643)
  ·
    refine ⟨167337906776990705845302965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111558604517993803896868643 167337906776990705845302965)
    ·
      refine ⟨15687928760342878672997153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167337906776990705845302965 15687928760342878672997153)
      ·
        refine ⟨11765946570257159004747865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15687928760342878672997153 11765946570257159004747865)
        ·
          refine ⟨8824459927692869253560899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11765946570257159004747865 8824459927692869253560899)
          ·
            refine ⟨13236689891539303880341349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824459927692869253560899 13236689891539303880341349)
            ·
              refine ⟨2481879354663619477564003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13236689891539303880341349 2481879354663619477564003)
              ·
                refine ⟨3722819031995429216346005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481879354663619477564003 3722819031995429216346005)
                ·
                  refine ⟨174507142124785744516219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3722819031995429216346005 174507142124785744516219)
                  ·
                    rfl

theorem cell23_3058663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 6].length) (baseStart_3058663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058663 prefixEnd_3058663 := by exact prefixLift 3058663
  have htrace : WordTrace (prefixWord ++ tailWord_3058663) baseStart_3058663 baseEnd_3058663 := by
    simpa [prefixWord, tailWord_3058663, baseEnd_3058663] using wordTrace_append hprefix tailTrace_3058663
  have hstable : (prefixWord ++ tailWord_3058663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058663).length < 2 ^ (prefixWord ++ tailWord_3058663).sum := by decide
  have hdescent : baseEnd_3058663 < baseStart_3058663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058677 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3058677 : Nat := 118140960795 + 3058677 * 2 ^ 59
def prefixEnd_3058677 : Nat := 4983230072969 + 3 ^ 40 * 3058677 * 2
def baseEnd_3058677 : Nat := 1570571467852234645870907

theorem tailTrace_3058677 : CollatzResearch.WordTrace tailWord_3058677 prefixEnd_3058677 1570571467852234645870907 := by
  unfold tailWord_3058677
  simp only [CollatzResearch.WordTrace]
  refine ⟨111559115139943084287878285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74372743426628722858585523 111559115139943084287878285)
  ·
    refine ⟨41834668177478656607954357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111559115139943084287878285 41834668177478656607954357)
    ·
      refine ⟨3922000141638624056995721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41834668177478656607954357 3922000141638624056995721)
      ·
        refine ⟨2941500106228968042746791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3922000141638624056995721 2941500106228968042746791)
        ·
          refine ⟨4412250159343452064120187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941500106228968042746791 4412250159343452064120187)
          ·
            refine ⟨6618375239015178096180281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412250159343452064120187 6618375239015178096180281)
            ·
              refine ⟨4963781429261383572135211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618375239015178096180281 4963781429261383572135211)
              ·
                refine ⟨7445672143892075358202817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963781429261383572135211 7445672143892075358202817)
                ·
                  refine ⟨5584254107919056518652113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445672143892075358202817 5584254107919056518652113)
                  ·
                    refine ⟨4188190580939292388989085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584254107919056518652113 4188190580939292388989085)
                    ·
                      refine ⟨1570571467852234645870907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4188190580939292388989085 1570571467852234645870907)
                      ·
                        rfl

theorem cell23_3058677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3058677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058677 prefixEnd_3058677 := by exact prefixLift 3058677
  have htrace : WordTrace (prefixWord ++ tailWord_3058677) baseStart_3058677 baseEnd_3058677 := by
    simpa [prefixWord, tailWord_3058677, baseEnd_3058677] using wordTrace_append hprefix tailTrace_3058677
  have hstable : (prefixWord ++ tailWord_3058677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058677).length < 2 ^ (prefixWord ++ tailWord_3058677).sum := by decide
  have hdescent : baseEnd_3058677 < baseStart_3058677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058693 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_3058693 : Nat := 118140960795 + 3058693 * 2 ^ 59
def prefixEnd_3058693 : Nat := 4983230072969 + 3 ^ 40 * 3058693 * 2
def baseEnd_3058693 : Nat := 523526561180902194423611

theorem tailTrace_3058693 : CollatzResearch.WordTrace tailWord_3058693 prefixEnd_3058693 523526561180902194423611 := by
  unfold tailWord_3058693
  simp only [CollatzResearch.WordTrace]
  refine ⟨111559698707885119020460733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74373132471923412680307155 111559698707885119020460733)
  ·
    refine ⟨41834887015456919632672775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111559698707885119020460733 41834887015456919632672775)
    ·
      refine ⟨62752330523185379449009163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41834887015456919632672775 62752330523185379449009163)
      ·
        refine ⟨94128495784778069173513745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62752330523185379449009163 94128495784778069173513745)
        ·
          refine ⟨70596371838583551880135309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94128495784778069173513745 70596371838583551880135309)
          ·
            refine ⟨26473639439468831955050741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70596371838583551880135309 26473639439468831955050741)
            ·
              refine ⟨2481903697450202995786007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26473639439468831955050741 2481903697450202995786007)
              ·
                refine ⟨3722855546175304493679011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481903697450202995786007 3722855546175304493679011)
                ·
                  refine ⟨5584283319262956740518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722855546175304493679011 5584283319262956740518517)
                  ·
                    refine ⟨523526561180902194423611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584283319262956740518517 523526561180902194423611)
                    ·
                      rfl

theorem cell23_3058693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_3058693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058693 prefixEnd_3058693 := by exact prefixLift 3058693
  have htrace : WordTrace (prefixWord ++ tailWord_3058693) baseStart_3058693 baseEnd_3058693 := by
    simpa [prefixWord, tailWord_3058693, baseEnd_3058693] using wordTrace_append hprefix tailTrace_3058693
  have hstable : (prefixWord ++ tailWord_3058693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058693).length < 2 ^ (prefixWord ++ tailWord_3058693).sum := by decide
  have hdescent : baseEnd_3058693 < baseStart_3058693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058723 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 2, 4]
def baseStart_3058723 : Nat := 118140960795 + 3058723 * 2 ^ 59
def prefixEnd_3058723 : Nat := 4983230072969 + 3 ^ 40 * 3058723 * 2
def baseEnd_3058723 : Nat := 523531695987447155298565

theorem tailTrace_3058723 : CollatzResearch.WordTrace tailWord_3058723 prefixEnd_3058723 523531695987447155298565 := by
  unfold tailWord_3058723
  simp only [CollatzResearch.WordTrace]
  refine ⟨111560792897776434144052823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74373861931850956096035215 111560792897776434144052823)
  ·
    refine ⟨167341189346664651216079235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111560792897776434144052823 167341189346664651216079235)
    ·
      refine ⟨251011784019996976824118853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167341189346664651216079235 251011784019996976824118853)
      ·
        refine ⟨47064709503749433154522285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251011784019996976824118853 47064709503749433154522285)
        ·
          refine ⟨17649266063906037432945857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47064709503749433154522285 17649266063906037432945857)
          ·
            refine ⟨13236949547929528074709393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17649266063906037432945857 13236949547929528074709393)
            ·
              refine ⟨9927712160947146056032045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13236949547929528074709393 9927712160947146056032045)
              ·
                refine ⟨3722892060355179771012017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9927712160947146056032045 3722892060355179771012017)
                ·
                  refine ⟨2792169045266384828259013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722892060355179771012017 2792169045266384828259013)
                  ·
                    refine ⟨523531695987447155298565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792169045266384828259013 523531695987447155298565)
                    ·
                      rfl

theorem cell23_3058723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 4].length) (baseStart_3058723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058723 prefixEnd_3058723 := by exact prefixLift 3058723
  have htrace : WordTrace (prefixWord ++ tailWord_3058723) baseStart_3058723 baseEnd_3058723 := by
    simpa [prefixWord, tailWord_3058723, baseEnd_3058723] using wordTrace_append hprefix tailTrace_3058723
  have hstable : (prefixWord ++ tailWord_3058723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058723).length < 2 ^ (prefixWord ++ tailWord_3058723).sum := by decide
  have hdescent : baseEnd_3058723 < baseStart_3058723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058736 : List Nat := [2, 1, 1, 1, 2, 4, 5, 7]
def baseStart_3058736 : Nat := 118140960795 + 3058736 * 2 ^ 59
def prefixEnd_3058736 : Nat := 4983230072969 + 3 ^ 40 * 3058736 * 2
def baseEnd_3058736 : Nat := 58170435674475922779005

theorem tailTrace_3058736 : CollatzResearch.WordTrace tailWord_3058736 prefixEnd_3058736 58170435674475922779005 := by
  unfold tailWord_3058736
  simp only [CollatzResearch.WordTrace]
  refine ⟨55780633523364668682138031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74374178031152891576184041 55780633523364668682138031)
  ·
    refine ⟨83670950285047003023207047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55780633523364668682138031 83670950285047003023207047)
    ·
      refine ⟨125506425427570504534810571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83670950285047003023207047 125506425427570504534810571)
      ·
        refine ⟨188259638141355756802215857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125506425427570504534810571 188259638141355756802215857)
        ·
          refine ⟨141194728606016817601661893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188259638141355756802215857 141194728606016817601661893)
          ·
            refine ⟨26474011613628153300311605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141194728606016817601661893 26474011613628153300311605)
            ·
              refine ⟨2481938588777639371904213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26474011613628153300311605 2481938588777639371904213)
              ·
                refine ⟨58170435674475922779005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2481938588777639371904213 58170435674475922779005)
                ·
                  rfl

theorem cell23_3058736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 7].length) (baseStart_3058736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058736 prefixEnd_3058736 := by exact prefixLift 3058736
  have htrace : WordTrace (prefixWord ++ tailWord_3058736) baseStart_3058736 baseEnd_3058736 := by
    simpa [prefixWord, tailWord_3058736, baseEnd_3058736] using wordTrace_append hprefix tailTrace_3058736
  have hstable : (prefixWord ++ tailWord_3058736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058736).length < 2 ^ (prefixWord ++ tailWord_3058736).sum := by decide
  have hdescent : baseEnd_3058736 < baseStart_3058736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058774 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3058774 : Nat := 118140960795 + 3058774 * 2 ^ 59
def prefixEnd_3058774 : Nat := 4983230072969 + 3 ^ 40 * 3058774 * 2
def baseEnd_3058774 : Nat := 523540425158573588785987

theorem tailTrace_3058774 : CollatzResearch.WordTrace tailWord_3058774 prefixEnd_3058774 523540425158573588785987 := by
  unfold tailWord_3058774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972665813786979365884961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74375102013727779902772917 6972665813786979365884961)
  ·
    refine ⟨5229499360340234524413721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6972665813786979365884961 5229499360340234524413721)
    ·
      refine ⟨3922124520255175893310291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5229499360340234524413721 3922124520255175893310291)
      ·
        refine ⟨5883186780382763839965437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922124520255175893310291 5883186780382763839965437)
        ·
          refine ⟨2206195042643536439987039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5883186780382763839965437 2206195042643536439987039)
          ·
            refine ⟨3309292563965304659980559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206195042643536439987039 3309292563965304659980559)
            ·
              refine ⟨4963938845947956989970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309292563965304659980559 4963938845947956989970839)
              ·
                refine ⟨7445908268921935484956259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963938845947956989970839 7445908268921935484956259)
                ·
                  refine ⟨11168862403382903227434389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445908268921935484956259 11168862403382903227434389)
                  ·
                    refine ⟨523540425158573588785987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11168862403382903227434389 523540425158573588785987)
                    ·
                      rfl

theorem cell23_3058774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3058774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058774 prefixEnd_3058774 := by exact prefixLift 3058774
  have htrace : WordTrace (prefixWord ++ tailWord_3058774) baseStart_3058774 baseEnd_3058774 := by
    simpa [prefixWord, tailWord_3058774, baseEnd_3058774] using wordTrace_append hprefix tailTrace_3058774
  have hstable : (prefixWord ++ tailWord_3058774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058774).length < 2 ^ (prefixWord ++ tailWord_3058774).sum := by decide
  have hdescent : baseEnd_3058774 < baseStart_3058774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058816 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3058816 : Nat := 118140960795 + 3058816 * 2 ^ 59
def prefixEnd_3058816 : Nat := 4983230072969 + 3 ^ 40 * 3058816 * 2
def baseEnd_3058816 : Nat := 1570642841663209602032767

theorem tailTrace_3058816 : CollatzResearch.WordTrace tailWord_3058816 prefixEnd_3058816 1570642841663209602032767 := by
  unfold tailWord_3058816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55782092443219755513594151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74376123257626340684792201 55782092443219755513594151)
  ·
    refine ⟨83673138664829633270391227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55782092443219755513594151 83673138664829633270391227)
    ·
      refine ⟨125509707997244449905586841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83673138664829633270391227 125509707997244449905586841)
      ·
        refine ⟨94132280997933337429190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125509707997244449905586841 94132280997933337429190131)
        ·
          refine ⟨141198421496900006143785197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94132280997933337429190131 141198421496900006143785197)
          ·
            refine ⟨52949408061337502303919449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141198421496900006143785197 52949408061337502303919449)
            ·
              refine ⟨39712056046003126727939587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52949408061337502303919449 39712056046003126727939587)
              ·
                refine ⟨59568084069004690091909381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39712056046003126727939587 59568084069004690091909381)
                ·
                  refine ⟨11169015762938379392233009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59568084069004690091909381 11169015762938379392233009)
                  ·
                    refine ⟨8376761822203784544174757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11169015762938379392233009 8376761822203784544174757)
                    ·
                      refine ⟨1570642841663209602032767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8376761822203784544174757 1570642841663209602032767)
                      ·
                        rfl

theorem cell23_3058816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3058816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058816 prefixEnd_3058816 := by exact prefixLift 3058816
  have htrace : WordTrace (prefixWord ++ tailWord_3058816) baseStart_3058816 baseEnd_3058816 := by
    simpa [prefixWord, tailWord_3058816, baseEnd_3058816] using wordTrace_append hprefix tailTrace_3058816
  have hstable : (prefixWord ++ tailWord_3058816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058816).length < 2 ^ (prefixWord ++ tailWord_3058816).sum := by decide
  have hdescent : baseEnd_3058816 < baseStart_3058816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058873 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_3058873 : Nat := 118140960795 + 3058873 * 2 ^ 59
def prefixEnd_3058873 : Nat := 4983230072969 + 3 ^ 40 * 3058873 * 2
def baseEnd_3058873 : Nat := 523557370020171959673335

theorem tailTrace_3058873 : CollatzResearch.WordTrace tailWord_3058873 prefixEnd_3058873 523557370020171959673335 := by
  unfold tailWord_3058873
  simp only [CollatzResearch.WordTrace]
  refine ⟨111566263847233009762013273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74377509231488673174675515 111566263847233009762013273)
  ·
    refine ⟨83674697885424757321509955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111566263847233009762013273 83674697885424757321509955)
    ·
      refine ⟨125512046828137135982264933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83674697885424757321509955 125512046828137135982264933)
      ·
        refine ⟨23533508780275712996674675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125512046828137135982264933 23533508780275712996674675)
        ·
          refine ⟨35300263170413569495012013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23533508780275712996674675 35300263170413569495012013)
          ·
            refine ⟨13237598688905088560629505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35300263170413569495012013 13237598688905088560629505)
            ·
              refine ⟨9928199016678816420472129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13237598688905088560629505 9928199016678816420472129)
              ·
                refine ⟨7446149262509112315354097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9928199016678816420472129 7446149262509112315354097)
                ·
                  refine ⟨5584611946881834236515573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446149262509112315354097 5584611946881834236515573)
                  ·
                    refine ⟨523557370020171959673335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584611946881834236515573 523557370020171959673335)
                    ·
                      rfl

theorem cell23_3058873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_3058873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058873 prefixEnd_3058873 := by exact prefixLift 3058873
  have htrace : WordTrace (prefixWord ++ tailWord_3058873) baseStart_3058873 baseEnd_3058873 := by
    simpa [prefixWord, tailWord_3058873, baseEnd_3058873] using wordTrace_append hprefix tailTrace_3058873
  have hstable : (prefixWord ++ tailWord_3058873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058873).length < 2 ^ (prefixWord ++ tailWord_3058873).sum := by decide
  have hdescent : baseEnd_3058873 < baseStart_3058873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058903 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 5, 4]
def baseStart_3058903 : Nat := 118140960795 + 3058903 * 2 ^ 59
def prefixEnd_3058903 : Nat := 4983230072969 + 3 ^ 40 * 3058903 * 2
def baseEnd_3058903 : Nat := 523562504826716920548289

theorem tailTrace_3058903 : CollatzResearch.WordTrace tailWord_3058903 prefixEnd_3058903 523562504826716920548289 := by
  unfold tailWord_3058903
  simp only [CollatzResearch.WordTrace]
  refine ⟨111567358037124324885605363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74378238691416216590403575 111567358037124324885605363)
  ·
    refine ⟨167351037055686487328408045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111567358037124324885605363 167351037055686487328408045)
    ·
      refine ⟨62756638895882432748153017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167351037055686487328408045 62756638895882432748153017)
      ·
        refine ⟨47067479171911824561114763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62756638895882432748153017 47067479171911824561114763)
        ·
          refine ⟨70601218757867736841672145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47067479171911824561114763 70601218757867736841672145)
          ·
            refine ⟨52950914068400802631254109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70601218757867736841672145 52950914068400802631254109)
            ·
              refine ⟨19856592775650300986720291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52950914068400802631254109 19856592775650300986720291)
              ·
                refine ⟨29784889163475451480080437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19856592775650300986720291 29784889163475451480080437)
                ·
                  refine ⟨2792333359075823576257541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29784889163475451480080437 2792333359075823576257541)
                  ·
                    refine ⟨523562504826716920548289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792333359075823576257541 523562504826716920548289)
                    ·
                      rfl

theorem cell23_3058903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_3058903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058903 prefixEnd_3058903 := by exact prefixLift 3058903
  have htrace : WordTrace (prefixWord ++ tailWord_3058903) baseStart_3058903 baseEnd_3058903 := by
    simpa [prefixWord, tailWord_3058903, baseEnd_3058903] using wordTrace_append hprefix tailTrace_3058903
  have hstable : (prefixWord ++ tailWord_3058903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058903).length < 2 ^ (prefixWord ++ tailWord_3058903).sum := by decide
  have hdescent : baseEnd_3058903 < baseStart_3058903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058980 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_3058980 : Nat := 118140960795 + 3058980 * 2 ^ 59
def prefixEnd_3058980 : Nat := 4983230072969 + 3 ^ 40 * 3058980 * 2
def baseEnd_3058980 : Nat := 523575684163515653460671

theorem tailTrace_3058980 : CollatzResearch.WordTrace tailWord_3058980 prefixEnd_3058980 523575684163515653460671 := by
  unfold tailWord_3058980
  simp only [CollatzResearch.WordTrace]
  refine ⟨55785083228922683518079197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74380110971896911357438929 55785083228922683518079197)
  ·
    refine ⟨20919406210846006319279699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55785083228922683518079197 20919406210846006319279699)
    ·
      refine ⟨31379109316269009478919549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20919406210846006319279699 31379109316269009478919549)
      ·
        refine ⟨11767165993600878554594831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31379109316269009478919549 11767165993600878554594831)
        ·
          refine ⟨17650748990401317831892247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11767165993600878554594831 17650748990401317831892247)
          ·
            refine ⟨26476123485601976747838371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17650748990401317831892247 26476123485601976747838371)
            ·
              refine ⟨39714185228402965121757557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26476123485601976747838371 39714185228402965121757557)
              ·
                refine ⟨3723204865162777980164771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39714185228402965121757557 3723204865162777980164771)
                ·
                  refine ⟨5584807297744166970247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723204865162777980164771 5584807297744166970247157)
                  ·
                    refine ⟨523575684163515653460671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584807297744166970247157 523575684163515653460671)
                    ·
                      rfl

theorem cell23_3058980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_3058980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058980 prefixEnd_3058980 := by exact prefixLift 3058980
  have htrace : WordTrace (prefixWord ++ tailWord_3058980) baseStart_3058980 baseEnd_3058980 := by
    simpa [prefixWord, tailWord_3058980, baseEnd_3058980] using wordTrace_append hprefix tailTrace_3058980
  have hstable : (prefixWord ++ tailWord_3058980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058980).length < 2 ^ (prefixWord ++ tailWord_3058980).sum := by decide
  have hdescent : baseEnd_3058980 < baseStart_3058980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3058994 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3058994 : Nat := 118140960795 + 3058994 * 2 ^ 59
def prefixEnd_3058994 : Nat := 4983230072969 + 3 ^ 40 * 3058994 * 2
def baseEnd_3058994 : Nat := 1570734241219709905606949

theorem tailTrace_3058994 : CollatzResearch.WordTrace tailWord_3058994 prefixEnd_3058994 1570734241219709905606949 := by
  unfold tailWord_3058994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892669269948661856792009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74380451386529764951445357 27892669269948661856792009)
  ·
    refine ⟨20919501952461496392594007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27892669269948661856792009 20919501952461496392594007)
    ·
      refine ⟨31379252928692244588891011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20919501952461496392594007 31379252928692244588891011)
      ·
        refine ⟨47068879393038366883336517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31379252928692244588891011 47068879393038366883336517)
        ·
          refine ⟨8825414886194693790625597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47068879393038366883336517 8825414886194693790625597)
          ·
            refine ⟨3309530582323010171484599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8825414886194693790625597 3309530582323010171484599)
            ·
              refine ⟨4964295873484515257226899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309530582323010171484599 4964295873484515257226899)
              ·
                refine ⟨7446443810226772885840349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964295873484515257226899 7446443810226772885840349)
                ·
                  refine ⟨2792416428835039832190131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7446443810226772885840349 2792416428835039832190131)
                  ·
                    refine ⟨4188624643252559748285197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792416428835039832190131 4188624643252559748285197)
                    ·
                      refine ⟨1570734241219709905606949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4188624643252559748285197 1570734241219709905606949)
                      ·
                        rfl

theorem cell23_3058994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3058994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3058994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3058994 prefixEnd_3058994 := by exact prefixLift 3058994
  have htrace : WordTrace (prefixWord ++ tailWord_3058994) baseStart_3058994 baseEnd_3058994 := by
    simpa [prefixWord, tailWord_3058994, baseEnd_3058994] using wordTrace_append hprefix tailTrace_3058994
  have hstable : (prefixWord ++ tailWord_3058994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3058994).length < 2 ^ (prefixWord ++ tailWord_3058994).sum := by decide
  have hdescent : baseEnd_3058994 < baseStart_3058994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3058994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059013 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_3059013 : Nat := 118140960795 + 3059013 * 2 ^ 59
def prefixEnd_3059013 : Nat := 4983230072969 + 3 ^ 40 * 3059013 * 2
def baseEnd_3059013 : Nat := 1570743997352145331269361

theorem tailTrace_3059013 : CollatzResearch.WordTrace tailWord_3059013 prefixEnd_3059013 1570743997352145331269361 := by
  unfold tailWord_3059013
  simp only [CollatzResearch.WordTrace]
  refine ⟨111571370066725813672109693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74380913377817209114739795 111571370066725813672109693)
  ·
    refine ⟨41839263775022180127041135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111571370066725813672109693 41839263775022180127041135)
    ·
      refine ⟨62758895662533270190561703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41839263775022180127041135 62758895662533270190561703)
      ·
        refine ⟨94138343493799905285842555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62758895662533270190561703 94138343493799905285842555)
        ·
          refine ⟨141207515240699857928763833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94138343493799905285842555 141207515240699857928763833)
          ·
            refine ⟨105905636430524893446572875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141207515240699857928763833 105905636430524893446572875)
            ·
              refine ⟨158858454645787340169859313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105905636430524893446572875 158858454645787340169859313)
              ·
                refine ⟨119143840984340505127394485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158858454645787340169859313 119143840984340505127394485)
                ·
                  refine ⟨11169735092281922355693233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119143840984340505127394485 11169735092281922355693233)
                  ·
                    refine ⟨8377301319211441766769925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11169735092281922355693233 8377301319211441766769925)
                    ·
                      refine ⟨1570743997352145331269361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8377301319211441766769925 1570743997352145331269361)
                      ·
                        rfl

theorem cell23_3059013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_3059013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059013 prefixEnd_3059013 := by exact prefixLift 3059013
  have htrace : WordTrace (prefixWord ++ tailWord_3059013) baseStart_3059013 baseEnd_3059013 := by
    simpa [prefixWord, tailWord_3059013, baseEnd_3059013] using wordTrace_append hprefix tailTrace_3059013
  have hstable : (prefixWord ++ tailWord_3059013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059013).length < 2 ^ (prefixWord ++ tailWord_3059013).sum := by decide
  have hdescent : baseEnd_3059013 < baseStart_3059013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059017 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 3, 2, 2]
def baseStart_3059017 : Nat := 118140960795 + 3059017 * 2 ^ 59
def prefixEnd_3059017 : Nat := 4983230072969 + 3 ^ 40 * 3059017 * 2
def baseEnd_3059017 : Nat := 1570746051274763315619343

theorem tailTrace_3059017 : CollatzResearch.WordTrace tailWord_3059017 prefixEnd_3059017 1570746051274763315619343 := by
  unfold tailWord_3059017
  simp only [CollatzResearch.WordTrace]
  refine ⟨111571515958711322355255305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74381010639140881570170203 111571515958711322355255305)
  ·
    refine ⟨83678636969033491766441479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111571515958711322355255305 83678636969033491766441479)
    ·
      refine ⟨125517955453550237649662219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83678636969033491766441479 125517955453550237649662219)
      ·
        refine ⟨188276933180325356474493329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125517955453550237649662219 188276933180325356474493329)
        ·
          refine ⟨141207699885244017355869997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188276933180325356474493329 141207699885244017355869997)
          ·
            refine ⟨52952887456966506508451249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141207699885244017355869997 52952887456966506508451249)
            ·
              refine ⟨39714665592724879881338437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52952887456966506508451249 39714665592724879881338437)
              ·
                refine ⟨7446499798635914977750957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39714665592724879881338437 7446499798635914977750957)
                ·
                  refine ⟨2792437424488468116656609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7446499798635914977750957 2792437424488468116656609)
                  ·
                    refine ⟨2094328068366351087492457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2792437424488468116656609 2094328068366351087492457)
                    ·
                      refine ⟨1570746051274763315619343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094328068366351087492457 1570746051274763315619343)
                      ·
                        rfl

theorem cell23_3059017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2, 2].length) (baseStart_3059017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059017 prefixEnd_3059017 := by exact prefixLift 3059017
  have htrace : WordTrace (prefixWord ++ tailWord_3059017) baseStart_3059017 baseEnd_3059017 := by
    simpa [prefixWord, tailWord_3059017, baseEnd_3059017] using wordTrace_append hprefix tailTrace_3059017
  have hstable : (prefixWord ++ tailWord_3059017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059017).length < 2 ^ (prefixWord ++ tailWord_3059017).sum := by decide
  have hdescent : baseEnd_3059017 < baseStart_3059017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059067 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 3]
def baseStart_3059067 : Nat := 118140960795 + 3059067 * 2 ^ 59
def prefixEnd_3059067 : Nat := 4983230072969 + 3 ^ 40 * 3059067 * 2
def baseEnd_3059067 : Nat := 1570771725307488119994113

theorem tailTrace_3059067 : CollatzResearch.WordTrace tailWord_3059067 prefixEnd_3059067 1570771725307488119994113 := by
  unfold tailWord_3059067
  simp only [CollatzResearch.WordTrace]
  refine ⟨111573339608530180894575455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74382226405686787263050303 111573339608530180894575455)
  ·
    refine ⟨167360009412795271341863183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111573339608530180894575455 167360009412795271341863183)
    ·
      refine ⟨251040014119192907012794775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167360009412795271341863183 251040014119192907012794775)
      ·
        refine ⟨376560021178789360519192163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251040014119192907012794775 376560021178789360519192163)
        ·
          refine ⟨564840031768184040778788245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376560021178789360519192163 564840031768184040778788245)
          ·
            refine ⟨26476876489133626911505699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 564840031768184040778788245 26476876489133626911505699)
            ·
              refine ⟨39715314733700440367258549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26476876489133626911505699 39715314733700440367258549)
              ·
                refine ⟨3723310756284416284430489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39715314733700440367258549 3723310756284416284430489)
                ·
                  refine ⟨2792483067213312213322867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723310756284416284430489 2792483067213312213322867)
                  ·
                    refine ⟨4188724600819968319984301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792483067213312213322867 4188724600819968319984301)
                    ·
                      refine ⟨1570771725307488119994113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4188724600819968319984301 1570771725307488119994113)
                      ·
                        rfl

theorem cell23_3059067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 3].length) (baseStart_3059067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059067 prefixEnd_3059067 := by exact prefixLift 3059067
  have htrace : WordTrace (prefixWord ++ tailWord_3059067) baseStart_3059067 baseEnd_3059067 := by
    simpa [prefixWord, tailWord_3059067, baseEnd_3059067] using wordTrace_append hprefix tailTrace_3059067
  have hstable : (prefixWord ++ tailWord_3059067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059067).length < 2 ^ (prefixWord ++ tailWord_3059067).sum := by decide
  have hdescent : baseEnd_3059067 < baseStart_3059067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059074 : List Nat := [3, 4, 2, 1, 1, 2, 3, 7]
def baseStart_3059074 : Nat := 118140960795 + 3059074 * 2 ^ 59
def prefixEnd_3059074 : Nat := 4983230072969 + 3 ^ 40 * 3059074 * 2
def baseEnd_3059074 : Nat := 58176863691558133059503

theorem tailTrace_3059074 : CollatzResearch.WordTrace tailWord_3059074 prefixEnd_3059074 58176863691558133059503 := by
  unfold tailWord_3059074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27893398729876205272520069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74382396613003214060053517 27893398729876205272520069)
  ·
    refine ⟨5230012261851788488597513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27893398729876205272520069 5230012261851788488597513)
    ·
      refine ⟨3922509196388841366448135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230012261851788488597513 3922509196388841366448135)
      ·
        refine ⟨5883763794583262049672203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922509196388841366448135 5883763794583262049672203)
        ·
          refine ⟨8825645691874893074508305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883763794583262049672203 8825645691874893074508305)
          ·
            refine ⟨6619234268906169805881229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8825645691874893074508305 6619234268906169805881229)
            ·
              refine ⟨2482212850839813677205461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6619234268906169805881229 2482212850839813677205461)
              ·
                refine ⟨58176863691558133059503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2482212850839813677205461 58176863691558133059503)
                ·
                  rfl

theorem cell23_3059074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_3059074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059074 prefixEnd_3059074 := by exact prefixLift 3059074
  have htrace : WordTrace (prefixWord ++ tailWord_3059074) baseStart_3059074 baseEnd_3059074 := by
    simpa [prefixWord, tailWord_3059074, baseEnd_3059074] using wordTrace_append hprefix tailTrace_3059074
  have hstable : (prefixWord ++ tailWord_3059074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059074).length < 2 ^ (prefixWord ++ tailWord_3059074).sum := by decide
  have hdescent : baseEnd_3059074 < baseStart_3059074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059077 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_3059077 : Nat := 118140960795 + 3059077 * 2 ^ 59
def prefixEnd_3059077 : Nat := 4983230072969 + 3 ^ 40 * 3059077 * 2
def baseEnd_3059077 : Nat := 1570776860114033080869067

theorem tailTrace_3059077 : CollatzResearch.WordTrace tailWord_3059077 prefixEnd_3059077 1570776860114033080869067 := by
  unfold tailWord_3059077
  simp only [CollatzResearch.WordTrace]
  refine ⟨111573704338493952602439485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74382469558995968401626323 111573704338493952602439485)
  ·
    refine ⟨41840139126935232225914807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111573704338493952602439485 41840139126935232225914807)
    ·
      refine ⟨62760208690402848338872211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41840139126935232225914807 62760208690402848338872211)
      ·
        refine ⟨94140313035604272508308317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62760208690402848338872211 94140313035604272508308317)
        ·
          refine ⟨35302617388351602190615619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94140313035604272508308317 35302617388351602190615619)
          ·
            refine ⟨52953926082527403285923429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35302617388351602190615619 52953926082527403285923429)
            ·
              refine ⟨9928861140473888116110643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52953926082527403285923429 9928861140473888116110643)
              ·
                refine ⟨14893291710710832174165965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928861140473888116110643 14893291710710832174165965)
                ·
                  refine ⟨5584984391516562065312237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14893291710710832174165965 5584984391516562065312237)
                  ·
                    refine ⟨2094369146818710774492089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5584984391516562065312237 2094369146818710774492089)
                    ·
                      refine ⟨1570776860114033080869067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094369146818710774492089 1570776860114033080869067)
                      ·
                        rfl

theorem cell23_3059077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_3059077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059077 prefixEnd_3059077 := by exact prefixLift 3059077
  have htrace : WordTrace (prefixWord ++ tailWord_3059077) baseStart_3059077 baseEnd_3059077 := by
    simpa [prefixWord, tailWord_3059077, baseEnd_3059077] using wordTrace_append hprefix tailTrace_3059077
  have hstable : (prefixWord ++ tailWord_3059077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059077).length < 2 ^ (prefixWord ++ tailWord_3059077).sum := by decide
  have hdescent : baseEnd_3059077 < baseStart_3059077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059083 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 8]
def baseStart_3059083 : Nat := 118140960795 + 3059083 * 2 ^ 59
def prefixEnd_3059083 : Nat := 4983230072969 + 3 ^ 40 * 3059083 * 2
def baseEnd_3059083 : Nat := 523593313665986685798013

theorem tailTrace_3059083 : CollatzResearch.WordTrace tailWord_3059083 prefixEnd_3059083 523593313665986685798013 := by
  unfold tailWord_3059083
  simp only [CollatzResearch.WordTrace]
  refine ⟨111573923176472215627157903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74382615450981477084771935 111573923176472215627157903)
  ·
    refine ⟨167360884764708323440736855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111573923176472215627157903 167360884764708323440736855)
    ·
      refine ⟨251041327147062485161105283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167360884764708323440736855 251041327147062485161105283)
      ·
        refine ⟨376561990720593727741657925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251041327147062485161105283 376561990720593727741657925)
        ·
          refine ⟨70605373260111323951560861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376561990720593727741657925 70605373260111323951560861)
          ·
            refine ⟨26477014972541746481835323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70605373260111323951560861 26477014972541746481835323)
            ·
              refine ⟨39715522458812619722752985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26477014972541746481835323 39715522458812619722752985)
              ·
                refine ⟨29786641844109464792064739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39715522458812619722752985 29786641844109464792064739)
                ·
                  refine ⟨44679962766164197188097109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29786641844109464792064739 44679962766164197188097109)
                  ·
                    refine ⟨523593313665986685798013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44679962766164197188097109 523593313665986685798013)
                    ·
                      rfl

theorem cell23_3059083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_3059083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059083 prefixEnd_3059083 := by exact prefixLift 3059083
  have htrace : WordTrace (prefixWord ++ tailWord_3059083) baseStart_3059083 baseEnd_3059083 := by
    simpa [prefixWord, tailWord_3059083, baseEnd_3059083] using wordTrace_append hprefix tailTrace_3059083
  have hstable : (prefixWord ++ tailWord_3059083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059083).length < 2 ^ (prefixWord ++ tailWord_3059083).sum := by decide
  have hdescent : baseEnd_3059083 < baseStart_3059083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059101 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3059101 : Nat := 118140960795 + 3059101 * 2 ^ 59
def prefixEnd_3059101 : Nat := 4983230072969 + 3 ^ 40 * 3059101 * 2
def baseEnd_3059101 : Nat := 1570789183649740986968957

theorem tailTrace_3059101 : CollatzResearch.WordTrace tailWord_3059101 prefixEnd_3059101 1570789183649740986968957 := by
  unfold tailWord_3059101
  simp only [CollatzResearch.WordTrace]
  refine ⟨111574579690407004701313157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74383053126938003134208771 111574579690407004701313157)
  ·
    refine ⟨20920233691951313381496217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111574579690407004701313157 20920233691951313381496217)
    ·
      refine ⟨15690175268963485036122163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20920233691951313381496217 15690175268963485036122163)
      ·
        refine ⟨23535262903445227554183245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15690175268963485036122163 23535262903445227554183245)
        ·
          refine ⟨8825723588791960332818717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23535262903445227554183245 8825723588791960332818717)
          ·
            refine ⟨3309646345796985124807019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8825723588791960332818717 3309646345796985124807019)
            ·
              refine ⟨4964469518695477687210529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309646345796985124807019 4964469518695477687210529)
              ·
                refine ⟨3723352139021608265407897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964469518695477687210529 3723352139021608265407897)
                ·
                  refine ⟨2792514104266206199055923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723352139021608265407897 2792514104266206199055923)
                  ·
                    refine ⟨4188771156399309298583885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792514104266206199055923 4188771156399309298583885)
                    ·
                      refine ⟨1570789183649740986968957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4188771156399309298583885 1570789183649740986968957)
                      ·
                        rfl

theorem cell23_3059101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3059101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059101 prefixEnd_3059101 := by exact prefixLift 3059101
  have htrace : WordTrace (prefixWord ++ tailWord_3059101) baseStart_3059101 baseEnd_3059101 := by
    simpa [prefixWord, tailWord_3059101, baseEnd_3059101] using wordTrace_append hprefix tailTrace_3059101
  have hstable : (prefixWord ++ tailWord_3059101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059101).length < 2 ^ (prefixWord ++ tailWord_3059101).sum := by decide
  have hdescent : baseEnd_3059101 < baseStart_3059101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059117 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3059117 : Nat := 118140960795 + 3059117 * 2 ^ 59
def prefixEnd_3059117 : Nat := 4983230072969 + 3 ^ 40 * 3059117 * 2
def baseEnd_3059117 : Nat := 523599133113404308122961

theorem tailTrace_3059117 : CollatzResearch.WordTrace tailWord_3059117 prefixEnd_3059117 523599133113404308122961 := by
  unfold tailWord_3059117
  simp only [CollatzResearch.WordTrace]
  refine ⟨111575163258349039433895605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74383442172232692955930403 111575163258349039433895605)
  ·
    refine ⟨10460171555470222446927713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111575163258349039433895605 10460171555470222446927713)
    ·
      refine ⟨7845128666602666835195785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10460171555470222446927713 7845128666602666835195785)
      ·
        refine ⟨5883846499952000126396839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845128666602666835195785 5883846499952000126396839)
        ·
          refine ⟨8825769749928000189595259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883846499952000126396839 8825769749928000189595259)
          ·
            refine ⟨13238654624892000284392889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8825769749928000189595259 13238654624892000284392889)
            ·
              refine ⟨9928990968669000213294667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13238654624892000284392889 9928990968669000213294667)
              ·
                refine ⟨14893486453003500319942001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928990968669000213294667 14893486453003500319942001)
                ·
                  refine ⟨11170114839752625239956501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14893486453003500319942001 11170114839752625239956501)
                  ·
                    refine ⟨523599133113404308122961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11170114839752625239956501 523599133113404308122961)
                    ·
                      rfl

theorem cell23_3059117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3059117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059117 prefixEnd_3059117 := by exact prefixLift 3059117
  have htrace : WordTrace (prefixWord ++ tailWord_3059117) baseStart_3059117 baseEnd_3059117 := by
    simpa [prefixWord, tailWord_3059117, baseEnd_3059117] using wordTrace_append hprefix tailTrace_3059117
  have hstable : (prefixWord ++ tailWord_3059117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059117).length < 2 ^ (prefixWord ++ tailWord_3059117).sum := by decide
  have hdescent : baseEnd_3059117 < baseStart_3059117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059123 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_3059123 : Nat := 118140960795 + 3059123 * 2 ^ 59
def prefixEnd_3059123 : Nat := 4983230072969 + 3 ^ 40 * 3059123 * 2
def baseEnd_3059123 : Nat := 1570800480224139900893855

theorem tailTrace_3059123 : CollatzResearch.WordTrace tailWord_3059123 prefixEnd_3059123 1570800480224139900893855 := by
  unfold tailWord_3059123
  simp only [CollatzResearch.WordTrace]
  refine ⟨111575382096327302458614023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74383588064218201639076015 111575382096327302458614023)
  ·
    refine ⟨167363073144490953687921035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111575382096327302458614023 167363073144490953687921035)
    ·
      refine ⟨251044609716736430531881553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167363073144490953687921035 251044609716736430531881553)
      ·
        refine ⟨188283457287552322898911165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251044609716736430531881553 188283457287552322898911165)
        ·
          refine ⟨70606296482832121087091687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188283457287552322898911165 70606296482832121087091687)
          ·
            refine ⟨105909444724248181630637531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70606296482832121087091687 105909444724248181630637531)
            ·
              refine ⟨158864167086372272445956297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105909444724248181630637531 158864167086372272445956297)
              ·
                refine ⟨119148125314779204334467223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158864167086372272445956297 119148125314779204334467223)
                ·
                  refine ⟨178722187972168806501700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119148125314779204334467223 178722187972168806501700835)
                  ·
                    refine ⟨268083281958253209752551253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178722187972168806501700835 268083281958253209752551253)
                    ·
                      refine ⟨1570800480224139900893855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 268083281958253209752551253 1570800480224139900893855)
                      ·
                        rfl

theorem cell23_3059123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_3059123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059123 prefixEnd_3059123 := by exact prefixLift 3059123
  have htrace : WordTrace (prefixWord ++ tailWord_3059123) baseStart_3059123 baseEnd_3059123 := by
    simpa [prefixWord, tailWord_3059123, baseEnd_3059123] using wordTrace_append hprefix tailTrace_3059123
  have hstable : (prefixWord ++ tailWord_3059123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059123).length < 2 ^ (prefixWord ++ tailWord_3059123).sum := by decide
  have hdescent : baseEnd_3059123 < baseStart_3059123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059147 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 5]
def baseStart_3059147 : Nat := 118140960795 + 3059147 * 2 ^ 59
def prefixEnd_3059147 : Nat := 4983230072969 + 3 ^ 40 * 3059147 * 2
def baseEnd_3059147 : Nat := 174534755973316422999305

theorem tailTrace_3059147 : CollatzResearch.WordTrace tailWord_3059147 prefixEnd_3059147 174534755973316422999305 := by
  unfold tailWord_3059147
  simp only [CollatzResearch.WordTrace]
  refine ⟨111576257448240354557487695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74384171632160236371658463 111576257448240354557487695)
  ·
    refine ⟨167364386172360531836231543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111576257448240354557487695 167364386172360531836231543)
    ·
      refine ⟨251046579258540797754347315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167364386172360531836231543 251046579258540797754347315)
      ·
        refine ⟨376569868887811196631520973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251046579258540797754347315 376569868887811196631520973)
        ·
          refine ⟨141213700832929198736820365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376569868887811196631520973 141213700832929198736820365)
          ·
            refine ⟨52955137812348449526307637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141213700832929198736820365 52955137812348449526307637)
            ·
              refine ⟨4964544169907667143091341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52955137812348449526307637 4964544169907667143091341)
              ·
                refine ⟨1861704063715375178659253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4964544169907667143091341 1861704063715375178659253)
                ·
                  refine ⟨174534755973316422999305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861704063715375178659253 174534755973316422999305)
                  ·
                    rfl

theorem cell23_3059147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 5].length) (baseStart_3059147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059147 prefixEnd_3059147 := by exact prefixLift 3059147
  have htrace : WordTrace (prefixWord ++ tailWord_3059147) baseStart_3059147 baseEnd_3059147 := by
    simpa [prefixWord, tailWord_3059147, baseEnd_3059147] using wordTrace_append hprefix tailTrace_3059147
  have hstable : (prefixWord ++ tailWord_3059147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059147).length < 2 ^ (prefixWord ++ tailWord_3059147).sum := by decide
  have hdescent : baseEnd_3059147 < baseStart_3059147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059160 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3059160 : Nat := 118140960795 + 3059160 * 2 ^ 59
def prefixEnd_3059160 : Nat := 4983230072969 + 3 ^ 40 * 3059160 * 2
def baseEnd_3059160 : Nat := 523606493002785418710395

theorem tailTrace_3059160 : CollatzResearch.WordTrace tailWord_3059160 prefixEnd_3059160 523606493002785418710395 := by
  unfold tailWord_3059160
  simp only [CollatzResearch.WordTrace]
  refine ⟨55788365798596628888855467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74384487731462171851807289 55788365798596628888855467)
  ·
    refine ⟨83682548697894943333283201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55788365798596628888855467 83682548697894943333283201)
    ·
      refine ⟨62761911523421207499962401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83682548697894943333283201 62761911523421207499962401)
      ·
        refine ⟨47071433642565905624971801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62761911523421207499962401 47071433642565905624971801)
        ·
          refine ⟨35303575231924429218728851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47071433642565905624971801 35303575231924429218728851)
          ·
            refine ⟨52955362847886643828093277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35303575231924429218728851 52955362847886643828093277)
            ·
              refine ⟨19858261067957491435534979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52955362847886643828093277 19858261067957491435534979)
              ·
                refine ⟨29787391601936237153302469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19858261067957491435534979 29787391601936237153302469)
                ·
                  refine ⟨5585135925363044466244213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29787391601936237153302469 5585135925363044466244213)
                  ·
                    refine ⟨523606493002785418710395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5585135925363044466244213 523606493002785418710395)
                    ·
                      rfl

theorem cell23_3059160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3059160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059160 prefixEnd_3059160 := by exact prefixLift 3059160
  have htrace : WordTrace (prefixWord ++ tailWord_3059160) baseStart_3059160 baseEnd_3059160 := by
    simpa [prefixWord, tailWord_3059160, baseEnd_3059160] using wordTrace_append hprefix tailTrace_3059160
  have hstable : (prefixWord ++ tailWord_3059160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059160).length < 2 ^ (prefixWord ++ tailWord_3059160).sum := by decide
  have hdescent : baseEnd_3059160 < baseStart_3059160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059167 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 5, 2]
def baseStart_3059167 : Nat := 118140960795 + 3059167 * 2 ^ 59
def prefixEnd_3059167 : Nat := 4983230072969 + 3 ^ 40 * 3059167 * 2
def baseEnd_3059167 : Nat := 1570823073372937728743653

theorem tailTrace_3059167 : CollatzResearch.WordTrace tailWord_3059167 prefixEnd_3059167 1570823073372937728743653 := by
  unfold tailWord_3059167
  simp only [CollatzResearch.WordTrace]
  refine ⟨111576986908167897973215755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74384657938778598648810503 111576986908167897973215755)
  ·
    refine ⟨167365480362251846959823633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111576986908167897973215755 167365480362251846959823633)
    ·
      refine ⟨125524110271688885219867725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167365480362251846959823633 125524110271688885219867725)
      ·
        refine ⟨47071541351883331957450397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125524110271688885219867725 47071541351883331957450397)
        ·
          refine ⟨17651828006956249484043899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47071541351883331957450397 17651828006956249484043899)
          ·
            refine ⟨26477742010434374226065849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17651828006956249484043899 26477742010434374226065849)
            ·
              refine ⟨19858306507825780669549387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26477742010434374226065849 19858306507825780669549387)
              ·
                refine ⟨29787459761738671004324081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19858306507825780669549387 29787459761738671004324081)
                ·
                  refine ⟨22340594821304003253243061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29787459761738671004324081 22340594821304003253243061)
                  ·
                    refine ⟨2094430764497250304991537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22340594821304003253243061 2094430764497250304991537)
                    ·
                      refine ⟨1570823073372937728743653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094430764497250304991537 1570823073372937728743653)
                      ·
                        rfl

theorem cell23_3059167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_3059167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059167 prefixEnd_3059167 := by exact prefixLift 3059167
  have htrace : WordTrace (prefixWord ++ tailWord_3059167) baseStart_3059167 baseEnd_3059167 := by
    simpa [prefixWord, tailWord_3059167, baseEnd_3059167] using wordTrace_append hprefix tailTrace_3059167
  have hstable : (prefixWord ++ tailWord_3059167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059167).length < 2 ^ (prefixWord ++ tailWord_3059167).sum := by decide
  have hdescent : baseEnd_3059167 < baseStart_3059167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059180 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3059180 : Nat := 118140960795 + 3059180 * 2 ^ 59
def prefixEnd_3059180 : Nat := 4983230072969 + 3 ^ 40 * 3059180 * 2
def baseEnd_3059180 : Nat := 1570829748621446177881093

theorem tailTrace_3059180 : CollatzResearch.WordTrace tailWord_3059180 prefixEnd_3059180 1570829748621446177881093 := by
  unfold tailWord_3059180
  simp only [CollatzResearch.WordTrace]
  refine ⟨55788730528560400596719497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74384974038080534128959329 55788730528560400596719497)
  ·
    refine ⟨41841547896420300447539623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55788730528560400596719497 41841547896420300447539623)
    ·
      refine ⟨62762321844630450671309435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41841547896420300447539623 62762321844630450671309435)
      ·
        refine ⟨94143482766945676006964153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62762321844630450671309435 94143482766945676006964153)
        ·
          refine ⟨70607612075209257005223115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94143482766945676006964153 70607612075209257005223115)
          ·
            refine ⟨105911418112813885507834673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70607612075209257005223115 105911418112813885507834673)
            ·
              refine ⟨79433563584610414130876005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105911418112813885507834673 79433563584610414130876005)
              ·
                refine ⟨14893793172114452649539251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79433563584610414130876005 14893793172114452649539251)
                ·
                  refine ⟨22340689758171678974308877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14893793172114452649539251 22340689758171678974308877)
                  ·
                    refine ⟨8377758659314379615365829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22340689758171678974308877 8377758659314379615365829)
                    ·
                      refine ⟨1570829748621446177881093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8377758659314379615365829 1570829748621446177881093)
                      ·
                        rfl

theorem cell23_3059180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3059180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059180 prefixEnd_3059180 := by exact prefixLift 3059180
  have htrace : WordTrace (prefixWord ++ tailWord_3059180) baseStart_3059180 baseEnd_3059180 := by
    simpa [prefixWord, tailWord_3059180, baseEnd_3059180] using wordTrace_append hprefix tailTrace_3059180
  have hstable : (prefixWord ++ tailWord_3059180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059180).length < 2 ^ (prefixWord ++ tailWord_3059180).sum := by decide
  have hdescent : baseEnd_3059180 < baseStart_3059180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059197 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3059197 : Nat := 118140960795 + 3059197 * 2 ^ 59
def prefixEnd_3059197 : Nat := 4983230072969 + 3 ^ 40 * 3059197 * 2
def baseEnd_3059197 : Nat := 1570838477792572611368515

theorem tailTrace_3059197 : CollatzResearch.WordTrace tailWord_3059197 prefixEnd_3059197 1570838477792572611368515 := by
  unfold tailWord_3059197
  simp only [CollatzResearch.WordTrace]
  refine ⟨111578081098059213096807845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74385387398706142064538563 111578081098059213096807845)
  ·
    refine ⟨20920890205886102455651471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111578081098059213096807845 20920890205886102455651471)
    ·
      refine ⟨31381335308829153683477207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20920890205886102455651471 31381335308829153683477207)
      ·
        refine ⟨47072002963243730525215811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31381335308829153683477207 47072002963243730525215811)
        ·
          refine ⟨70608004444865595787823717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47072002963243730525215811 70608004444865595787823717)
          ·
            refine ⟨13239000833412299210216947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70608004444865595787823717 13239000833412299210216947)
            ·
              refine ⟨19858501250118448815325421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13239000833412299210216947 19858501250118448815325421)
              ·
                refine ⟨7446937968794418305747033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19858501250118448815325421 7446937968794418305747033)
                ·
                  refine ⟨5585203476595813729310275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446937968794418305747033 5585203476595813729310275)
                  ·
                    refine ⟨8377805214893720593965413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585203476595813729310275 8377805214893720593965413)
                    ·
                      refine ⟨1570838477792572611368515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8377805214893720593965413 1570838477792572611368515)
                      ·
                        rfl

theorem cell23_3059197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3059197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059197 prefixEnd_3059197 := by exact prefixLift 3059197
  have htrace : WordTrace (prefixWord ++ tailWord_3059197) baseStart_3059197 baseEnd_3059197 := by
    simpa [prefixWord, tailWord_3059197, baseEnd_3059197] using wordTrace_append hprefix tailTrace_3059197
  have hstable : (prefixWord ++ tailWord_3059197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059197).length < 2 ^ (prefixWord ++ tailWord_3059197).sum := by decide
  have hdescent : baseEnd_3059197 < baseStart_3059197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059217 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_3059217 : Nat := 118140960795 + 3059217 * 2 ^ 59
def prefixEnd_3059217 : Nat := 4983230072969 + 3 ^ 40 * 3059217 * 2
def baseEnd_3059217 : Nat := 1570848747405662533118423

theorem tailTrace_3059217 : CollatzResearch.WordTrace tailWord_3059217 prefixEnd_3059217 1570848747405662533118423 := by
  unfold tailWord_3059217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111578810557986756512535905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74385873705324504341690603 111578810557986756512535905)
  ·
    refine ⟨83684107918490067384401929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111578810557986756512535905 83684107918490067384401929)
    ·
      refine ⟨62763080938867550538301447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83684107918490067384401929 62763080938867550538301447)
      ·
        refine ⟨94144621408301325807452171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62763080938867550538301447 94144621408301325807452171)
        ·
          refine ⟨141216932112451988711178257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94144621408301325807452171 141216932112451988711178257)
          ·
            refine ⟨105912699084338991533383693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141216932112451988711178257 105912699084338991533383693)
            ·
              refine ⟨39717262156627121825018885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105912699084338991533383693 39717262156627121825018885)
              ·
                refine ⟨7446986654367585342191041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39717262156627121825018885 7446986654367585342191041)
                ·
                  refine ⟨5585239990775689006643281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446986654367585342191041 5585239990775689006643281)
                  ·
                    refine ⟨4188929993081766754982461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585239990775689006643281 4188929993081766754982461)
                    ·
                      refine ⟨1570848747405662533118423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4188929993081766754982461 1570848747405662533118423)
                      ·
                        rfl

theorem cell23_3059217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_3059217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059217 prefixEnd_3059217 := by exact prefixLift 3059217
  have htrace : WordTrace (prefixWord ++ tailWord_3059217) baseStart_3059217 baseEnd_3059217 := by
    simpa [prefixWord, tailWord_3059217, baseEnd_3059217] using wordTrace_append hprefix tailTrace_3059217
  have hstable : (prefixWord ++ tailWord_3059217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059217).length < 2 ^ (prefixWord ++ tailWord_3059217).sum := by decide
  have hdescent : baseEnd_3059217 < baseStart_3059217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059271 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 6]
def baseStart_3059271 : Nat := 118140960795 + 3059271 * 2 ^ 59
def prefixEnd_3059271 : Nat := 4983230072969 + 3 ^ 40 * 3059271 * 2
def baseEnd_3059271 : Nat := 174541830595667257982575

theorem tailTrace_3059271 : CollatzResearch.WordTrace tailWord_3059271 prefixEnd_3059271 174541830595667257982575 := by
  unfold tailWord_3059271
  simp only [CollatzResearch.WordTrace]
  refine ⟨111580780099791123735001667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74387186733194082490001111 111580780099791123735001667)
  ·
    refine ⟨167371170149686685602502501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111580780099791123735001667 167371170149686685602502501)
    ·
      refine ⟨31382094403066253550469219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167371170149686685602502501 31382094403066253550469219)
      ·
        refine ⟨47073141604599380325703829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31382094403066253550469219 47073141604599380325703829)
        ·
          refine ⟨2206553512715595952767367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47073141604599380325703829 2206553512715595952767367)
          ·
            refine ⟨3309830269073393929151051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206553512715595952767367 3309830269073393929151051)
            ·
              refine ⟨4964745403610090893726577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309830269073393929151051 4964745403610090893726577)
              ·
                refine ⟨3723559052707568170294933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964745403610090893726577 3723559052707568170294933)
                ·
                  refine ⟨174541830595667257982575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3723559052707568170294933 174541830595667257982575)
                  ·
                    rfl

theorem cell23_3059271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 6].length) (baseStart_3059271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059271 prefixEnd_3059271 := by exact prefixLift 3059271
  have htrace : WordTrace (prefixWord ++ tailWord_3059271) baseStart_3059271 baseEnd_3059271 := by
    simpa [prefixWord, tailWord_3059271, baseEnd_3059271] using wordTrace_append hprefix tailTrace_3059271
  have hstable : (prefixWord ++ tailWord_3059271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059271).length < 2 ^ (prefixWord ++ tailWord_3059271).sum := by decide
  have hdescent : baseEnd_3059271 < baseStart_3059271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059274 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_3059274 : Nat := 118140960795 + 3059274 * 2 ^ 59
def prefixEnd_3059274 : Nat := 4983230072969 + 3 ^ 40 * 3059274 * 2
def baseEnd_3059274 : Nat := 1570878015802968810105661

theorem tailTrace_3059274 : CollatzResearch.WordTrace tailWord_3059274 prefixEnd_3059274 1570878015802968810105661 := by
  unfold tailWord_3059274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895222379695063811840219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74387259679186836831573917 27895222379695063811840219)
  ·
    refine ⟨41842833569542595717760329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27895222379695063811840219 41842833569542595717760329)
    ·
      refine ⟨31382125177156946788320247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41842833569542595717760329 31382125177156946788320247)
      ·
        refine ⟨47073187765735420182480371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31382125177156946788320247 47073187765735420182480371)
        ·
          refine ⟨70609781648603130273720557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47073187765735420182480371 70609781648603130273720557)
          ·
            refine ⟨26478668118226173852645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70609781648603130273720557 26478668118226173852645209)
            ·
              refine ⟨19859001088669630389483907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26478668118226173852645209 19859001088669630389483907)
              ·
                refine ⟨29788501633004445584225861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19859001088669630389483907 29788501633004445584225861)
                ·
                  refine ⟨5585344056188333547042349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29788501633004445584225861 5585344056188333547042349)
                  ·
                    refine ⟨2094504021070625080140881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5585344056188333547042349 2094504021070625080140881)
                    ·
                      refine ⟨1570878015802968810105661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094504021070625080140881 1570878015802968810105661)
                      ·
                        rfl

theorem cell23_3059274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_3059274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059274 prefixEnd_3059274 := by exact prefixLift 3059274
  have htrace : WordTrace (prefixWord ++ tailWord_3059274) baseStart_3059274 baseEnd_3059274 := by
    simpa [prefixWord, tailWord_3059274, baseEnd_3059274] using wordTrace_append hprefix tailTrace_3059274
  have hstable : (prefixWord ++ tailWord_3059274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059274).length < 2 ^ (prefixWord ++ tailWord_3059274).sum := by decide
  have hdescent : baseEnd_3059274 < baseStart_3059274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059281 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_3059281 : Nat := 118140960795 + 3059281 * 2 ^ 59
def prefixEnd_3059281 : Nat := 4983230072969 + 3 ^ 40 * 3059281 * 2
def baseEnd_3059281 : Nat := 1570881610167550282718129

theorem tailTrace_3059281 : CollatzResearch.WordTrace tailWord_3059281 prefixEnd_3059281 1570881610167550282718129 := by
  unfold tailWord_3059281
  simp only [CollatzResearch.WordTrace]
  refine ⟨111581144829754895442865697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74387429886503263628577131 111581144829754895442865697)
  ·
    refine ⟨83685858622316171582149273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111581144829754895442865697 83685858622316171582149273)
    ·
      refine ⟨62764393966737128686611955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83685858622316171582149273 62764393966737128686611955)
      ·
        refine ⟨94146590950105693029917933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62764393966737128686611955 94146590950105693029917933)
        ·
          refine ⟨35304971606289634886219225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94146590950105693029917933 35304971606289634886219225)
          ·
            refine ⟨26478728704717226164664419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35304971606289634886219225 26478728704717226164664419)
            ·
              refine ⟨39718093057075839246996629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26478728704717226164664419 39718093057075839246996629)
              ·
                refine ⟨1861785612050429964702967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39718093057075839246996629 1861785612050429964702967)
                ·
                  refine ⟨2792678418075644947054451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861785612050429964702967 2792678418075644947054451)
                  ·
                    refine ⟨4189017627113467420581677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792678418075644947054451 4189017627113467420581677)
                    ·
                      refine ⟨1570881610167550282718129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189017627113467420581677 1570881610167550282718129)
                      ·
                        rfl

theorem cell23_3059281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_3059281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059281 prefixEnd_3059281 := by exact prefixLift 3059281
  have htrace : WordTrace (prefixWord ++ tailWord_3059281) baseStart_3059281 baseEnd_3059281 := by
    simpa [prefixWord, tailWord_3059281, baseEnd_3059281] using wordTrace_append hprefix tailTrace_3059281
  have hstable : (prefixWord ++ tailWord_3059281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059281).length < 2 ^ (prefixWord ++ tailWord_3059281).sum := by decide
  have hdescent : baseEnd_3059281 < baseStart_3059281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059307 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3]
def baseStart_3059307 : Nat := 118140960795 + 3059307 * 2 ^ 59
def prefixEnd_3059307 : Nat := 4983230072969 + 3 ^ 40 * 3059307 * 2
def baseEnd_3059307 : Nat := 1570894960664567180993009

theorem tailTrace_3059307 : CollatzResearch.WordTrace tailWord_3059307 prefixEnd_3059307 1570894960664567180993009 := by
  unfold tailWord_3059307
  simp only [CollatzResearch.WordTrace]
  refine ⟨111582093127660701883312175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74388062085107134588874783 111582093127660701883312175)
  ·
    refine ⟨167373139691491052824968263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111582093127660701883312175 167373139691491052824968263)
    ·
      refine ⟨251059709537236579237452395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167373139691491052824968263 251059709537236579237452395)
      ·
        refine ⟨376589564305854868856178593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251059709537236579237452395 376589564305854868856178593)
        ·
          refine ⟨282442173229391151642133945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376589564305854868856178593 282442173229391151642133945)
          ·
            refine ⟨211831629922043363731600459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282442173229391151642133945 211831629922043363731600459)
            ·
              refine ⟨317747444883065045597400689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211831629922043363731600459 317747444883065045597400689)
              ·
                refine ⟨238310583662298784198050517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317747444883065045597400689 238310583662298784198050517)
                ·
                  refine ⟨5585404304585127754641809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 238310583662298784198050517 5585404304585127754641809)
                  ·
                    refine ⟨4189053228438845815981357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585404304585127754641809 4189053228438845815981357)
                    ·
                      refine ⟨1570894960664567180993009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189053228438845815981357 1570894960664567180993009)
                      ·
                        rfl

theorem cell23_3059307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].length) (baseStart_3059307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059307 prefixEnd_3059307 := by exact prefixLift 3059307
  have htrace : WordTrace (prefixWord ++ tailWord_3059307) baseStart_3059307 baseEnd_3059307 := by
    simpa [prefixWord, tailWord_3059307, baseEnd_3059307] using wordTrace_append hprefix tailTrace_3059307
  have hstable : (prefixWord ++ tailWord_3059307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059307).length < 2 ^ (prefixWord ++ tailWord_3059307).sum := by decide
  have hdescent : baseEnd_3059307 < baseStart_3059307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059314 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3059314 : Nat := 118140960795 + 3059314 * 2 ^ 59
def prefixEnd_3059314 : Nat := 4983230072969 + 3 ^ 40 * 3059314 * 2
def baseEnd_3059314 : Nat := 523632851676382884535159

theorem tailTrace_3059314 : CollatzResearch.WordTrace tailWord_3059314 prefixEnd_3059314 523632851676382884535159 := by
  unfold tailWord_3059314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895587109658835519704249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74388232292423561385877997 27895587109658835519704249)
  ·
    refine ⟨20921690332244126639778187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27895587109658835519704249 20921690332244126639778187)
    ·
      refine ⟨31382535498366189959667281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20921690332244126639778187 31382535498366189959667281)
      ·
        refine ⟨23536901623774642469750461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31382535498366189959667281 23536901623774642469750461)
        ·
          refine ⟨8826338108915490926156423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23536901623774642469750461 8826338108915490926156423)
          ·
            refine ⟨13239507163373236389234635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8826338108915490926156423 13239507163373236389234635)
            ·
              refine ⟨19859260745059854583851953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13239507163373236389234635 19859260745059854583851953)
              ·
                refine ⟨14894445558794890937888965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19859260745059854583851953 14894445558794890937888965)
                ·
                  refine ⟨2792708542274042050854181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14894445558794890937888965 2792708542274042050854181)
                  ·
                    refine ⟨523632851676382884535159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792708542274042050854181 523632851676382884535159)
                    ·
                      rfl

theorem cell23_3059314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3059314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059314 prefixEnd_3059314 := by exact prefixLift 3059314
  have htrace : WordTrace (prefixWord ++ tailWord_3059314) baseStart_3059314 baseEnd_3059314 := by
    simpa [prefixWord, tailWord_3059314, baseEnd_3059314] using wordTrace_append hprefix tailTrace_3059314
  have hstable : (prefixWord ++ tailWord_3059314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059314).length < 2 ^ (prefixWord ++ tailWord_3059314).sum := by decide
  have hdescent : baseEnd_3059314 < baseStart_3059314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059338 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3059338 : Nat := 118140960795 + 3059338 * 2 ^ 59
def prefixEnd_3059338 : Nat := 4983230072969 + 3 ^ 40 * 3059338 * 2
def baseEnd_3059338 : Nat := 1570910878564856559705367

theorem tailTrace_3059338 : CollatzResearch.WordTrace tailWord_3059338 prefixEnd_3059338 1570910878564856559705367 := by
  unfold tailWord_3059338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895805947637098544422667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74388815860365596118460445 27895805947637098544422667)
  ·
    refine ⟨41843708921455647816634001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27895805947637098544422667 41843708921455647816634001)
    ·
      refine ⟨31382781691091735862475501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41843708921455647816634001 31382781691091735862475501)
      ·
        refine ⟨11768543134159400948428313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31382781691091735862475501 11768543134159400948428313)
        ·
          refine ⟨8826407350619550711321235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11768543134159400948428313 8826407350619550711321235)
          ·
            refine ⟨13239611025929326066981853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8826407350619550711321235 13239611025929326066981853)
            ·
              refine ⟨4964854134723497275118195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13239611025929326066981853 4964854134723497275118195)
              ·
                refine ⟨7447281202085245912677293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964854134723497275118195 7447281202085245912677293)
                ·
                  refine ⟨2792730450781967217253985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7447281202085245912677293 2792730450781967217253985)
                  ·
                    refine ⟨2094547838086475412940489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2792730450781967217253985 2094547838086475412940489)
                    ·
                      refine ⟨1570910878564856559705367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094547838086475412940489 1570910878564856559705367)
                      ·
                        rfl

theorem cell23_3059338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3059338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059338 prefixEnd_3059338 := by exact prefixLift 3059338
  have htrace : WordTrace (prefixWord ++ tailWord_3059338) baseStart_3059338 baseEnd_3059338 := by
    simpa [prefixWord, tailWord_3059338, baseEnd_3059338] using wordTrace_append hprefix tailTrace_3059338
  have hstable : (prefixWord ++ tailWord_3059338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059338).length < 2 ^ (prefixWord ++ tailWord_3059338).sum := by decide
  have hdescent : baseEnd_3059338 < baseStart_3059338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059348 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3059348 : Nat := 118140960795 + 3059348 * 2 ^ 59
def prefixEnd_3059348 : Nat := 4983230072969 + 3 ^ 40 * 3059348 * 2
def baseEnd_3059348 : Nat := 523638671123800506860107

theorem tailTrace_3059348 : CollatzResearch.WordTrace tailWord_3059348 prefixEnd_3059348 523638671123800506860107 := by
  unfold tailWord_3059348
  simp only [CollatzResearch.WordTrace]
  refine ⟨55791794260256082942777349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74389059013674777257036465 55791794260256082942777349)
  ·
    refine ⟨10460961423798015551770753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55791794260256082942777349 10460961423798015551770753)
    ·
      refine ⟨7845721067848511663828065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10460961423798015551770753 7845721067848511663828065)
      ·
        refine ⟨5884290800886383747871049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845721067848511663828065 5884290800886383747871049)
        ·
          refine ⟨4413218100664787810903287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5884290800886383747871049 4413218100664787810903287)
          ·
            refine ⟨6619827150997181716354931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413218100664787810903287 6619827150997181716354931)
            ·
              refine ⟨9929740726495772574532397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619827150997181716354931 9929740726495772574532397)
              ·
                refine ⟨3723652772435914715449649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929740726495772574532397 3723652772435914715449649)
                ·
                  refine ⟨2792739579326936036587237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723652772435914715449649 2792739579326936036587237)
                  ·
                    refine ⟨523638671123800506860107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792739579326936036587237 523638671123800506860107)
                    ·
                      rfl

theorem cell23_3059348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3059348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059348 prefixEnd_3059348 := by exact prefixLift 3059348
  have htrace : WordTrace (prefixWord ++ tailWord_3059348) baseStart_3059348 baseEnd_3059348 := by
    simpa [prefixWord, tailWord_3059348, baseEnd_3059348] using wordTrace_append hprefix tailTrace_3059348
  have hstable : (prefixWord ++ tailWord_3059348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059348).length < 2 ^ (prefixWord ++ tailWord_3059348).sum := by decide
  have hdescent : baseEnd_3059348 < baseStart_3059348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059358 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3059358 : Nat := 118140960795 + 3059358 * 2 ^ 59
def prefixEnd_3059358 : Nat := 4983230072969 + 3 ^ 40 * 3059358 * 2
def baseEnd_3059358 : Nat := 1570921148177946481455275

theorem tailTrace_3059358 : CollatzResearch.WordTrace tailWord_3059358 prefixEnd_3059358 1570921148177946481455275 := by
  unfold tailWord_3059358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947994156309492199177341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74389302166983958395612485 13947994156309492199177341)
  ·
    refine ⟨5230497808616059574691503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13947994156309492199177341 5230497808616059574691503)
    ·
      refine ⟨7845746712924089362037255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230497808616059574691503 7845746712924089362037255)
      ·
        refine ⟨11768620069386134043055883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7845746712924089362037255 11768620069386134043055883)
        ·
          refine ⟨17652930104079201064583825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768620069386134043055883 17652930104079201064583825)
          ·
            refine ⟨13239697578059400798437869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17652930104079201064583825 13239697578059400798437869)
            ·
              refine ⟨4964886591772275299414201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13239697578059400798437869 4964886591772275299414201)
              ·
                refine ⟨3723664943829206474560651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964886591772275299414201 3723664943829206474560651)
                ·
                  refine ⟨5585497415743809711840977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723664943829206474560651 5585497415743809711840977)
                  ·
                    refine ⟨4189123061807857283880733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585497415743809711840977 4189123061807857283880733)
                    ·
                      refine ⟨1570921148177946481455275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189123061807857283880733 1570921148177946481455275)
                      ·
                        rfl

theorem cell23_3059358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3059358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059358 prefixEnd_3059358 := by exact prefixLift 3059358
  have htrace : WordTrace (prefixWord ++ tailWord_3059358) baseStart_3059358 baseEnd_3059358 := by
    simpa [prefixWord, tailWord_3059358, baseEnd_3059358] using wordTrace_append hprefix tailTrace_3059358
  have hstable : (prefixWord ++ tailWord_3059358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059358).length < 2 ^ (prefixWord ++ tailWord_3059358).sum := by decide
  have hdescent : baseEnd_3059358 < baseStart_3059358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059388 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_3059388 : Nat := 118140960795 + 3059388 * 2 ^ 59
def prefixEnd_3059388 : Nat := 4983230072969 + 3 ^ 40 * 3059388 * 2
def baseEnd_3059388 : Nat := 1570936552597581364080137

theorem tailTrace_3059388 : CollatzResearch.WordTrace tailWord_3059388 prefixEnd_3059388 1570936552597581364080137 := by
  unfold tailWord_3059388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55792523720183626358505409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74390031626911501811340545 55792523720183626358505409)
  ·
    refine ⟨41844392790137719768879057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55792523720183626358505409 41844392790137719768879057)
    ·
      refine ⟨31383294592603289826659293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41844392790137719768879057 31383294592603289826659293)
      ·
        refine ⟨11768735472226233684997235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31383294592603289826659293 11768735472226233684997235)
        ·
          refine ⟨17653103208339350527495853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768735472226233684997235 17653103208339350527495853)
          ·
            refine ⟨6619913703127256447810945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17653103208339350527495853 6619913703127256447810945)
            ·
              refine ⟨4964935277345442335858209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6619913703127256447810945 4964935277345442335858209)
              ·
                refine ⟨3723701458009081751893657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4964935277345442335858209 3723701458009081751893657)
                ·
                  refine ⟨2792776093506811313920243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723701458009081751893657 2792776093506811313920243)
                  ·
                    refine ⟨4189164140260216970880365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792776093506811313920243 4189164140260216970880365)
                    ·
                      refine ⟨1570936552597581364080137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189164140260216970880365 1570936552597581364080137)
                      ·
                        rfl

theorem cell23_3059388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_3059388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059388 prefixEnd_3059388 := by exact prefixLift 3059388
  have htrace : WordTrace (prefixWord ++ tailWord_3059388) baseStart_3059388 baseEnd_3059388 := by
    simpa [prefixWord, tailWord_3059388, baseEnd_3059388] using wordTrace_append hprefix tailTrace_3059388
  have hstable : (prefixWord ++ tailWord_3059388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059388).length < 2 ^ (prefixWord ++ tailWord_3059388).sum := by decide
  have hdescent : baseEnd_3059388 < baseStart_3059388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059405 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3059405 : Nat := 118140960795 + 3059405 * 2 ^ 59
def prefixEnd_3059405 : Nat := 4983230072969 + 3 ^ 40 * 3059405 * 2
def baseEnd_3059405 : Nat := 1570945281768707797567559

theorem tailTrace_3059405 : CollatzResearch.WordTrace tailWord_3059405 prefixEnd_3059405 1570945281768707797567559 := by
  unfold tailWord_3059405
  simp only [CollatzResearch.WordTrace]
  refine ⟨111585667481305664620379669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74390444987537109746919779 111585667481305664620379669)
  ·
    refine ⟨5230578163186203029080297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111585667481305664620379669 5230578163186203029080297)
    ·
      refine ⟨3922933622389652271810223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230578163186203029080297 3922933622389652271810223)
      ·
        refine ⟨5884400433584478407715335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922933622389652271810223 5884400433584478407715335)
        ·
          refine ⟨8826600650376717611573003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884400433584478407715335 8826600650376717611573003)
          ·
            refine ⟨13239900975565076417359505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8826600650376717611573003 13239900975565076417359505)
            ·
              refine ⟨9929925731673807313019629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13239900975565076417359505 9929925731673807313019629)
              ·
                refine ⟨3723722149377677742382361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929925731673807313019629 3723722149377677742382361)
                ·
                  refine ⟨2792791612033258306786771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723722149377677742382361 2792791612033258306786771)
                  ·
                    refine ⟨4189187418049887460180157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792791612033258306786771 4189187418049887460180157)
                    ·
                      refine ⟨1570945281768707797567559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189187418049887460180157 1570945281768707797567559)
                      ·
                        rfl

theorem cell23_3059405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3059405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059405 prefixEnd_3059405 := by exact prefixLift 3059405
  have htrace : WordTrace (prefixWord ++ tailWord_3059405) baseStart_3059405 baseEnd_3059405 := by
    simpa [prefixWord, tailWord_3059405, baseEnd_3059405] using wordTrace_append hprefix tailTrace_3059405
  have hstable : (prefixWord ++ tailWord_3059405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059405).length < 2 ^ (prefixWord ++ tailWord_3059405).sum := by decide
  have hdescent : baseEnd_3059405 < baseStart_3059405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059417 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 9]
def baseStart_3059417 : Nat := 118140960795 + 3059417 * 2 ^ 59
def prefixEnd_3059417 : Nat := 4983230072969 + 3 ^ 40 * 3059417 * 2
def baseEnd_3059417 : Nat := 174550160392951305624167

theorem tailTrace_3059417 : CollatzResearch.WordTrace tailWord_3059417 prefixEnd_3059417 174550160392951305624167 := by
  unfold tailWord_3059417
  simp only [CollatzResearch.WordTrace]
  refine ⟨111586105157262190669816505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74390736771508127113211003 111586105157262190669816505)
  ·
    refine ⟨83689578867946643002362379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111586105157262190669816505 83689578867946643002362379)
    ·
      refine ⟨125534368301919964503543569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83689578867946643002362379 125534368301919964503543569)
      ·
        refine ⟨94150776226439973377657677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125534368301919964503543569 94150776226439973377657677)
        ·
          refine ⟨35306541084914990016621629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94150776226439973377657677 35306541084914990016621629)
          ·
            refine ⟨13239952906843121256233111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35306541084914990016621629 13239952906843121256233111)
            ·
              refine ⟨19859929360264681884349667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13239952906843121256233111 19859929360264681884349667)
              ·
                refine ⟨29789894040397022826524501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19859929360264681884349667 29789894040397022826524501)
                ·
                  refine ⟨174550160392951305624167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29789894040397022826524501 174550160392951305624167)
                  ·
                    rfl

theorem cell23_3059417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_3059417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059417 prefixEnd_3059417 := by exact prefixLift 3059417
  have htrace : WordTrace (prefixWord ++ tailWord_3059417) baseStart_3059417 baseEnd_3059417 := by
    simpa [prefixWord, tailWord_3059417, baseEnd_3059417] using wordTrace_append hprefix tailTrace_3059417
  have hstable : (prefixWord ++ tailWord_3059417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059417).length < 2 ^ (prefixWord ++ tailWord_3059417).sum := by decide
  have hdescent : baseEnd_3059417 < baseStart_3059417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059484 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3059484 : Nat := 118140960795 + 3059484 * 2 ^ 59
def prefixEnd_3059484 : Nat := 4983230072969 + 3 ^ 40 * 3059484 * 2
def baseEnd_3059484 : Nat := 1570985846740412988479695

theorem tailTrace_3059484 : CollatzResearch.WordTrace tailWord_3059484 prefixEnd_3059484 1570985846740412988479695 := by
  unfold tailWord_3059484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55794274424009730556252753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74392365898679640741670337 55794274424009730556252753)
  ·
    refine ⟨41845705818007297917189565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55794274424009730556252753 41845705818007297917189565)
    ·
      refine ⟨15692139681752736718946087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41845705818007297917189565 15692139681752736718946087)
      ·
        refine ⟨23538209522629105078419131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15692139681752736718946087 23538209522629105078419131)
        ·
          refine ⟨35307314283943657617628697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23538209522629105078419131 35307314283943657617628697)
          ·
            refine ⟨26480485712957743213221523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35307314283943657617628697 26480485712957743213221523)
            ·
              refine ⟨39720728569436614819832285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26480485712957743213221523 39720728569436614819832285)
              ·
                refine ⟨14895273213538730557437107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39720728569436614819832285 14895273213538730557437107)
                ·
                  refine ⟨22342909820308095836155661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14895273213538730557437107 22342909820308095836155661)
                  ·
                    refine ⟨8378591182615535938558373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22342909820308095836155661 8378591182615535938558373)
                    ·
                      refine ⟨1570985846740412988479695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8378591182615535938558373 1570985846740412988479695)
                      ·
                        rfl

theorem cell23_3059484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3059484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059484 prefixEnd_3059484 := by exact prefixLift 3059484
  have htrace : WordTrace (prefixWord ++ tailWord_3059484) baseStart_3059484 baseEnd_3059484 := by
    simpa [prefixWord, tailWord_3059484, baseEnd_3059484] using wordTrace_append hprefix tailTrace_3059484
  have hstable : (prefixWord ++ tailWord_3059484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059484).length < 2 ^ (prefixWord ++ tailWord_3059484).sum := by decide
  have hdescent : baseEnd_3059484 < baseStart_3059484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059538 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3059538 : Nat := 118140960795 + 3059538 * 2 ^ 59
def prefixEnd_3059538 : Nat := 4983230072969 + 3 ^ 40 * 3059538 * 2
def baseEnd_3059538 : Nat := 1571013574695755777204447

theorem tailTrace_3059538 : CollatzResearch.WordTrace tailWord_3059538 prefixEnd_3059538 1571013574695755777204447 := by
  unfold tailWord_3059538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897629597455957083742817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74393678926549218889980845 27897629597455957083742817)
  ·
    refine ⟨20923222198091967812807113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27897629597455957083742817 20923222198091967812807113)
    ·
      refine ⟨15692416648568975859605335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20923222198091967812807113 15692416648568975859605335)
      ·
        refine ⟨23538624972853463789408003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15692416648568975859605335 23538624972853463789408003)
        ·
          refine ⟨35307937459280195684112005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23538624972853463789408003 35307937459280195684112005)
          ·
            refine ⟨6620238273615036690771001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35307937459280195684112005 6620238273615036690771001)
            ·
              refine ⟨4965178705211277518078251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6620238273615036690771001 4965178705211277518078251)
              ·
                refine ⟨7447768057816916277117377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965178705211277518078251 7447768057816916277117377)
                ·
                  refine ⟨5585826043362687207838033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7447768057816916277117377 5585826043362687207838033)
                  ·
                    refine ⟨4189369532522015405878525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5585826043362687207838033 4189369532522015405878525)
                    ·
                      refine ⟨1571013574695755777204447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189369532522015405878525 1571013574695755777204447)
                      ·
                        rfl

theorem cell23_3059538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3059538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059538 prefixEnd_3059538 := by exact prefixLift 3059538
  have htrace : WordTrace (prefixWord ++ tailWord_3059538) baseStart_3059538 baseEnd_3059538 := by
    simpa [prefixWord, tailWord_3059538, baseEnd_3059538] using wordTrace_append hprefix tailTrace_3059538
  have hstable : (prefixWord ++ tailWord_3059538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059538).length < 2 ^ (prefixWord ++ tailWord_3059538).sum := by decide
  have hdescent : baseEnd_3059538 < baseStart_3059538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059562 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3059562 : Nat := 118140960795 + 3059562 * 2 ^ 59
def prefixEnd_3059562 : Nat := 4983230072969 + 3 ^ 40 * 3059562 * 2
def baseEnd_3059562 : Nat := 523675299410487894434779

theorem tailTrace_3059562 : CollatzResearch.WordTrace tailWord_3059562 prefixEnd_3059562 523675299410487894434779 := by
  unfold tailWord_3059562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897848435434220108461235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74394262494491253622563293 27897848435434220108461235)
  ·
    refine ⟨41846772653151330162691853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27897848435434220108461235 41846772653151330162691853)
    ·
      refine ⟨15692539744931748811009445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41846772653151330162691853 15692539744931748811009445)
      ·
        refine ⟨2942351202174702902064271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15692539744931748811009445 2942351202174702902064271)
        ·
          refine ⟨4413526803262054353096407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942351202174702902064271 4413526803262054353096407)
          ·
            refine ⟨6620290204893081529644611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413526803262054353096407 6620290204893081529644611)
            ·
              refine ⟨9930435307339622294466917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620290204893081529644611 9930435307339622294466917)
              ·
                refine ⟨1861956620126179180212547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9930435307339622294466917 1861956620126179180212547)
                ·
                  refine ⟨2792934930189268770318821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861956620126179180212547 2792934930189268770318821)
                  ·
                    refine ⟨523675299410487894434779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792934930189268770318821 523675299410487894434779)
                    ·
                      rfl

theorem cell23_3059562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3059562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059562 prefixEnd_3059562 := by exact prefixLift 3059562
  have htrace : WordTrace (prefixWord ++ tailWord_3059562) baseStart_3059562 baseEnd_3059562 := by
    simpa [prefixWord, tailWord_3059562, baseEnd_3059562] using wordTrace_append hprefix tailTrace_3059562
  have hstable : (prefixWord ++ tailWord_3059562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059562).length < 2 ^ (prefixWord ++ tailWord_3059562).sum := by decide
  have hdescent : baseEnd_3059562 < baseStart_3059562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059602 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3059602 : Nat := 118140960795 + 3059602 * 2 ^ 59
def prefixEnd_3059602 : Nat := 4983230072969 + 3 ^ 40 * 3059602 * 2
def baseEnd_3059602 : Nat := 1571046437457643526804153

theorem tailTrace_3059602 : CollatzResearch.WordTrace tailWord_3059602 prefixEnd_3059602 1571046437457643526804153 := by
  unfold tailWord_3059602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898213165397991816325265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74395235107727978176867373 27898213165397991816325265)
  ·
    refine ⟨20923659874048493862243949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27898213165397991816325265 20923659874048493862243949)
    ·
      refine ⟨7846372452768185198341481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20923659874048493862243949 7846372452768185198341481)
      ·
        refine ⟨5884779339576138898756111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7846372452768185198341481 5884779339576138898756111)
        ·
          refine ⟨8827169009364208348134167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884779339576138898756111 8827169009364208348134167)
          ·
            refine ⟨13240753514046312522201251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827169009364208348134167 13240753514046312522201251)
            ·
              refine ⟨19861130271069468783301877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13240753514046312522201251 19861130271069468783301877)
              ·
                refine ⟨1861980962912762698434551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19861130271069468783301877 1861980962912762698434551)
                ·
                  refine ⟨2792971444369144047651827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861980962912762698434551 2792971444369144047651827)
                  ·
                    refine ⟨4189457166553716071477741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792971444369144047651827 4189457166553716071477741)
                    ·
                      refine ⟨1571046437457643526804153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189457166553716071477741 1571046437457643526804153)
                      ·
                        rfl

theorem cell23_3059602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3059602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059602 prefixEnd_3059602 := by exact prefixLift 3059602
  have htrace : WordTrace (prefixWord ++ tailWord_3059602) baseStart_3059602 baseEnd_3059602 := by
    simpa [prefixWord, tailWord_3059602, baseEnd_3059602] using wordTrace_append hprefix tailTrace_3059602
  have hstable : (prefixWord ++ tailWord_3059602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059602).length < 2 ^ (prefixWord ++ tailWord_3059602).sum := by decide
  have hdescent : baseEnd_3059602 < baseStart_3059602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059645 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3059645 : Nat := 118140960795 + 3059645 * 2 ^ 59
def prefixEnd_3059645 : Nat := 4983230072969 + 3 ^ 40 * 3059645 * 2
def baseEnd_3059645 : Nat := 1571068517125786858566455

theorem tailTrace_3059645 : CollatzResearch.WordTrace tailWord_3059645 prefixEnd_3059645 1571068517125786858566455 := by
  unfold tailWord_3059645
  simp only [CollatzResearch.WordTrace]
  refine ⟨111594421000436185609116389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74396280666957457072744259 111594421000436185609116389)
  ·
    refine ⟨20923953937581784801709323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111594421000436185609116389 20923953937581784801709323)
    ·
      refine ⟨31385930906372677202563985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20923953937581784801709323 31385930906372677202563985)
      ·
        refine ⟨23539448179779507901922989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31385930906372677202563985 23539448179779507901922989)
        ·
          refine ⟨8827293067417315463221121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23539448179779507901922989 8827293067417315463221121)
          ·
            refine ⟨6620469800562986597415841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8827293067417315463221121 6620469800562986597415841)
            ·
              refine ⟨4965352350422239948061881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6620469800562986597415841 4965352350422239948061881)
              ·
                refine ⟨3724014262816679961046411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965352350422239948061881 3724014262816679961046411)
                ·
                  refine ⟨5586021394225019941569617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724014262816679961046411 5586021394225019941569617)
                  ·
                    refine ⟨4189516045668764956177213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586021394225019941569617 4189516045668764956177213)
                    ·
                      refine ⟨1571068517125786858566455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189516045668764956177213 1571068517125786858566455)
                      ·
                        rfl

theorem cell23_3059645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3059645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059645 prefixEnd_3059645 := by exact prefixLift 3059645
  have htrace : WordTrace (prefixWord ++ tailWord_3059645) baseStart_3059645 baseEnd_3059645 := by
    simpa [prefixWord, tailWord_3059645, baseEnd_3059645] using wordTrace_append hprefix tailTrace_3059645
  have hstable : (prefixWord ++ tailWord_3059645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059645).length < 2 ^ (prefixWord ++ tailWord_3059645).sum := by decide
  have hdescent : baseEnd_3059645 < baseStart_3059645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059658 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3059658 : Nat := 118140960795 + 3059658 * 2 ^ 59
def prefixEnd_3059658 : Nat := 4983230072969 + 3 ^ 40 * 3059658 * 2
def baseEnd_3059658 : Nat := 1571075192374295307703895

theorem tailTrace_3059658 : CollatzResearch.WordTrace tailWord_3059658 prefixEnd_3059658 1571075192374295307703895 := by
  unfold tailWord_3059658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898723787347272207334907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74396596766259392552893085 27898723787347272207334907)
  ·
    refine ⟨41848085681020908311002361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27898723787347272207334907 41848085681020908311002361)
    ·
      refine ⟨31386064260765681233251771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41848085681020908311002361 31386064260765681233251771)
      ·
        refine ⟨47079096391148521849877657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31386064260765681233251771 47079096391148521849877657)
        ·
          refine ⟨35309322293361391387408243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47079096391148521849877657 35309322293361391387408243)
          ·
            refine ⟨52963983440042087081112365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35309322293361391387408243 52963983440042087081112365)
            ·
              refine ⟨19861493790015782655417137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52963983440042087081112365 19861493790015782655417137)
              ·
                refine ⟨14896120342511836991562853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19861493790015782655417137 14896120342511836991562853)
                ·
                  refine ⟨2793022564220969435918035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14896120342511836991562853 2793022564220969435918035)
                  ·
                    refine ⟨4189533846331454153877053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793022564220969435918035 4189533846331454153877053)
                    ·
                      refine ⟨1571075192374295307703895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189533846331454153877053 1571075192374295307703895)
                      ·
                        rfl

theorem cell23_3059658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3059658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059658 prefixEnd_3059658 := by exact prefixLift 3059658
  have htrace : WordTrace (prefixWord ++ tailWord_3059658) baseStart_3059658 baseEnd_3059658 := by
    simpa [prefixWord, tailWord_3059658, baseEnd_3059658] using wordTrace_append hprefix tailTrace_3059658
  have hstable : (prefixWord ++ tailWord_3059658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059658).length < 2 ^ (prefixWord ++ tailWord_3059658).sum := by decide
  have hdescent : baseEnd_3059658 < baseStart_3059658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059702 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3059702 : Nat := 118140960795 + 3059702 * 2 ^ 59
def prefixEnd_3059702 : Nat := 4983230072969 + 3 ^ 40 * 3059702 * 2
def baseEnd_3059702 : Nat := 1571097785523093135553693

theorem tailTrace_3059702 : CollatzResearch.WordTrace tailWord_3059702 prefixEnd_3059702 1571097785523093135553693 := by
  unfold tailWord_3059702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974781247576855271496335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74397666640819789562627573 6974781247576855271496335)
  ·
    refine ⟨10462171871365282907244503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974781247576855271496335 10462171871365282907244503)
    ·
      refine ⟨15693257807047924360866755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462171871365282907244503 15693257807047924360866755)
      ·
        refine ⟨23539886710571886541300133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693257807047924360866755 23539886710571886541300133)
        ·
          refine ⟨4413728758232228726493775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23539886710571886541300133 4413728758232228726493775)
          ·
            refine ⟨6620593137348343089740663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413728758232228726493775 6620593137348343089740663)
            ·
              refine ⟨9930889706022514634610995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620593137348343089740663 9930889706022514634610995)
              ·
                refine ⟨14896334559033771951916493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9930889706022514634610995 14896334559033771951916493)
                ·
                  refine ⟨5586125459637664481968685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14896334559033771951916493 5586125459637664481968685)
                  ·
                    refine ⟨2094797047364124180738257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5586125459637664481968685 2094797047364124180738257)
                    ·
                      refine ⟨1571097785523093135553693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094797047364124180738257 1571097785523093135553693)
                      ·
                        rfl

theorem cell23_3059702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3059702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059702 prefixEnd_3059702 := by exact prefixLift 3059702
  have htrace : WordTrace (prefixWord ++ tailWord_3059702) baseStart_3059702 baseEnd_3059702 := by
    simpa [prefixWord, tailWord_3059702, baseEnd_3059702] using wordTrace_append hprefix tailTrace_3059702
  have hstable : (prefixWord ++ tailWord_3059702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059702).length < 2 ^ (prefixWord ++ tailWord_3059702).sum := by decide
  have hdescent : baseEnd_3059702 < baseStart_3059702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059768 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_3059768 : Nat := 118140960795 + 3059768 * 2 ^ 59
def prefixEnd_3059768 : Nat := 4983230072969 + 3 ^ 40 * 3059768 * 2
def baseEnd_3059768 : Nat := 523710558415429959109463

theorem tailTrace_3059768 : CollatzResearch.WordTrace tailWord_3059768 prefixEnd_3059768 523710558415429959109463 := by
  unfold tailWord_3059768
  simp only [CollatzResearch.WordTrace]
  refine ⟨55799453589495288807921979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74399271452660385077229305 55799453589495288807921979)
  ·
    refine ⟨83699180384242933211882969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55799453589495288807921979 83699180384242933211882969)
    ·
      refine ⟨62774385288182199908912227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83699180384242933211882969 62774385288182199908912227)
      ·
        refine ⟨94161577932273299863368341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62774385288182199908912227 94161577932273299863368341)
        ·
          refine ⟨4413823965575310931095391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94161577932273299863368341 4413823965575310931095391)
          ·
            refine ⟨6620735948362966396643087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413823965575310931095391 6620735948362966396643087)
            ·
              refine ⟨9931103922544449594964631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620735948362966396643087 9931103922544449594964631)
              ·
                refine ⟨14896655883816674392446947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931103922544449594964631 14896655883816674392446947)
                ·
                  refine ⟨22344983825725011588670421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896655883816674392446947 22344983825725011588670421)
                  ·
                    refine ⟨523710558415429959109463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22344983825725011588670421 523710558415429959109463)
                    ·
                      rfl

theorem cell23_3059768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_3059768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059768 prefixEnd_3059768 := by exact prefixLift 3059768
  have htrace : WordTrace (prefixWord ++ tailWord_3059768) baseStart_3059768 baseEnd_3059768 := by
    simpa [prefixWord, tailWord_3059768, baseEnd_3059768] using wordTrace_append hprefix tailTrace_3059768
  have hstable : (prefixWord ++ tailWord_3059768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059768).length < 2 ^ (prefixWord ++ tailWord_3059768).sum := by decide
  have hdescent : baseEnd_3059768 < baseStart_3059768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059771 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_3059771 : Nat := 118140960795 + 3059771 * 2 ^ 59
def prefixEnd_3059771 : Nat := 4983230072969 + 3 ^ 40 * 3059771 * 2
def baseEnd_3059771 : Nat := 1571133215688253365590875

theorem tailTrace_3059771 : CollatzResearch.WordTrace tailWord_3059771 prefixEnd_3059771 1571133215688253365590875 := by
  unfold tailWord_3059771
  simp only [CollatzResearch.WordTrace]
  refine ⟨111599016597979709128203167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74399344398653139418802111 111599016597979709128203167)
  ·
    refine ⟨167398524896969563692304751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111599016597979709128203167 167398524896969563692304751)
    ·
      refine ⟨251097787345454345538457127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167398524896969563692304751 251097787345454345538457127)
      ·
        refine ⟨376646681018181518307685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251097787345454345538457127 376646681018181518307685691)
        ·
          refine ⟨564970021527272277461528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376646681018181518307685691 564970021527272277461528537)
          ·
            refine ⟨423727516145454208096146403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564970021527272277461528537 423727516145454208096146403)
            ·
              refine ⟨635591274218181312144219605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423727516145454208096146403 635591274218181312144219605)
              ·
                refine ⟨14896670489488624503380147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 635591274218181312144219605 14896670489488624503380147)
                ·
                  refine ⟨22345005734232936755070221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896670489488624503380147 22345005734232936755070221)
                  ·
                    refine ⟨8379377150337351283151333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22345005734232936755070221 8379377150337351283151333)
                    ·
                      refine ⟨1571133215688253365590875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8379377150337351283151333 1571133215688253365590875)
                      ·
                        rfl

theorem cell23_3059771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_3059771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059771 prefixEnd_3059771 := by exact prefixLift 3059771
  have htrace : WordTrace (prefixWord ++ tailWord_3059771) baseStart_3059771 baseEnd_3059771 := by
    simpa [prefixWord, tailWord_3059771, baseEnd_3059771] using wordTrace_append hprefix tailTrace_3059771
  have hstable : (prefixWord ++ tailWord_3059771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059771).length < 2 ^ (prefixWord ++ tailWord_3059771).sum := by decide
  have hdescent : baseEnd_3059771 < baseStart_3059771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059788 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3059788 : Nat := 118140960795 + 3059788 * 2 ^ 59
def prefixEnd_3059788 : Nat := 4983230072969 + 3 ^ 40 * 3059788 * 2
def baseEnd_3059788 : Nat := 1571141944859379799078297

theorem tailTrace_3059788 : CollatzResearch.WordTrace tailWord_3059788 prefixEnd_3059788 1571141944859379799078297 := by
  unfold tailWord_3059788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55799818319459060515786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74399757759278747354381345 55799818319459060515786009)
  ·
    refine ⟨41849863739594295386839507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55799818319459060515786009 41849863739594295386839507)
    ·
      refine ⟨62774795609391443080259261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41849863739594295386839507 62774795609391443080259261)
      ·
        refine ⟨23540548353521791155097223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62774795609391443080259261 23540548353521791155097223)
        ·
          refine ⟨35310822530282686732645835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23540548353521791155097223 35310822530282686732645835)
          ·
            refine ⟨52966233795424030098968753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35310822530282686732645835 52966233795424030098968753)
            ·
              refine ⟨39724675346568022574226565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52966233795424030098968753 39724675346568022574226565)
              ·
                refine ⟨7448376627481504232667481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39724675346568022574226565 7448376627481504232667481)
                ·
                  refine ⟨5586282470611128174500611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448376627481504232667481 5586282470611128174500611)
                  ·
                    refine ⟨8379423705916692261750917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5586282470611128174500611 8379423705916692261750917)
                    ·
                      refine ⟨1571141944859379799078297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8379423705916692261750917 1571141944859379799078297)
                      ·
                        rfl

theorem cell23_3059788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3059788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059788 prefixEnd_3059788 := by exact prefixLift 3059788
  have htrace : WordTrace (prefixWord ++ tailWord_3059788) baseStart_3059788 baseEnd_3059788 := by
    simpa [prefixWord, tailWord_3059788, baseEnd_3059788] using wordTrace_append hprefix tailTrace_3059788
  have hstable : (prefixWord ++ tailWord_3059788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059788).length < 2 ^ (prefixWord ++ tailWord_3059788).sum := by decide
  have hdescent : baseEnd_3059788 < baseStart_3059788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059801 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3059801 : Nat := 118140960795 + 3059801 * 2 ^ 59
def prefixEnd_3059801 : Nat := 4983230072969 + 3 ^ 40 * 3059801 * 2
def baseEnd_3059801 : Nat := 1571148620107888248215737

theorem tailTrace_3059801 : CollatzResearch.WordTrace tailWord_3059801 prefixEnd_3059801 1571148620107888248215737 := by
  unfold tailWord_3059801
  simp only [CollatzResearch.WordTrace]
  refine ⟨111600110787871024251795257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74400073858580682834530171 111600110787871024251795257)
  ·
    refine ⟨83700083090903268188846443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111600110787871024251795257 83700083090903268188846443)
    ·
      refine ⟨125550124636354902283269665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83700083090903268188846443 125550124636354902283269665)
      ·
        refine ⟨94162593477266176712452249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125550124636354902283269665 94162593477266176712452249)
        ·
          refine ⟨70621945107949632534339187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94162593477266176712452249 70621945107949632534339187)
          ·
            refine ⟨105932917661924448801508781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70621945107949632534339187 105932917661924448801508781)
            ·
              refine ⟨39724844123221668300565793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105932917661924448801508781 39724844123221668300565793)
              ·
                refine ⟨29793633092416251225424345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39724844123221668300565793 29793633092416251225424345)
                ·
                  refine ⟨22345224819312188419068259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29793633092416251225424345 22345224819312188419068259)
                  ·
                    refine ⟨33517837228968282628602389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22345224819312188419068259 33517837228968282628602389)
                    ·
                      refine ⟨1571148620107888248215737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33517837228968282628602389 1571148620107888248215737)
                      ·
                        rfl

theorem cell23_3059801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3059801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059801 prefixEnd_3059801 := by exact prefixLift 3059801
  have htrace : WordTrace (prefixWord ++ tailWord_3059801) baseStart_3059801 baseEnd_3059801 := by
    simpa [prefixWord, tailWord_3059801, baseEnd_3059801] using wordTrace_append hprefix tailTrace_3059801
  have hstable : (prefixWord ++ tailWord_3059801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059801).length < 2 ^ (prefixWord ++ tailWord_3059801).sum := by decide
  have hdescent : baseEnd_3059801 < baseStart_3059801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059805 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3059805 : Nat := 118140960795 + 3059805 * 2 ^ 59
def prefixEnd_3059805 : Nat := 4983230072969 + 3 ^ 40 * 3059805 * 2
def baseEnd_3059805 : Nat := 1571150674030506232565719

theorem tailTrace_3059805 : CollatzResearch.WordTrace tailWord_3059805 prefixEnd_3059805 1571150674030506232565719 := by
  unfold tailWord_3059805
  simp only [CollatzResearch.WordTrace]
  refine ⟨111600256679856532934940869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74400171119904355289960579 111600256679856532934940869)
  ·
    refine ⟨20925048127473099925301413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111600256679856532934940869 20925048127473099925301413)
    ·
      refine ⟨3923446523901206235994015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20925048127473099925301413 3923446523901206235994015)
      ·
        refine ⟨5885169785851809353991023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923446523901206235994015 5885169785851809353991023)
        ·
          refine ⟨8827754678777714030986535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885169785851809353991023 8827754678777714030986535)
          ·
            refine ⟨13241632018166571046479803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827754678777714030986535 13241632018166571046479803)
            ·
              refine ⟨19862448027249856569719705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13241632018166571046479803 19862448027249856569719705)
              ·
                refine ⟨14896836020437392427289779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19862448027249856569719705 14896836020437392427289779)
                ·
                  refine ⟨22345254030656088640934669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896836020437392427289779 22345254030656088640934669)
                  ·
                    refine ⟨8379470261496033240350501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22345254030656088640934669 8379470261496033240350501)
                    ·
                      refine ⟨1571150674030506232565719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8379470261496033240350501 1571150674030506232565719)
                      ·
                        rfl

theorem cell23_3059805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3059805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059805 prefixEnd_3059805 := by exact prefixLift 3059805
  have htrace : WordTrace (prefixWord ++ tailWord_3059805) baseStart_3059805 baseEnd_3059805 := by
    simpa [prefixWord, tailWord_3059805, baseEnd_3059805] using wordTrace_append hprefix tailTrace_3059805
  have hstable : (prefixWord ++ tailWord_3059805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059805).length < 2 ^ (prefixWord ++ tailWord_3059805).sum := by decide
  have hdescent : baseEnd_3059805 < baseStart_3059805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059808 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3059808 : Nat := 118140960795 + 3059808 * 2 ^ 59
def prefixEnd_3059808 : Nat := 4983230072969 + 3 ^ 40 * 3059808 * 2
def baseEnd_3059808 : Nat := 1571152214472469720828205

theorem tailTrace_3059808 : CollatzResearch.WordTrace tailWord_3059808 prefixEnd_3059808 1571152214472469720828205 := by
  unfold tailWord_3059808
  simp only [CollatzResearch.WordTrace]
  refine ⟨55800183049422832223650039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74400244065897109631533385 55800183049422832223650039)
  ·
    refine ⟨83700274574134248335475059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55800183049422832223650039 83700274574134248335475059)
    ·
      refine ⟨125550411861201372503212589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83700274574134248335475059 125550411861201372503212589)
      ·
        refine ⟨47081404447950514688704721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125550411861201372503212589 47081404447950514688704721)
        ·
          refine ⟨35311053335962886016528541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47081404447950514688704721 35311053335962886016528541)
          ·
            refine ⟨13241645000986082256198203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35311053335962886016528541 13241645000986082256198203)
            ·
              refine ⟨19862467501479123384297305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13241645000986082256198203 19862467501479123384297305)
              ·
                refine ⟨14896850626109342538222979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19862467501479123384297305 14896850626109342538222979)
                ·
                  refine ⟨22345275939164013807334469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14896850626109342538222979 22345275939164013807334469)
                  ·
                    refine ⟨4189739238593252588875213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22345275939164013807334469 4189739238593252588875213)
                    ·
                      refine ⟨1571152214472469720828205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189739238593252588875213 1571152214472469720828205)
                      ·
                        rfl

theorem cell23_3059808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3059808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059808 prefixEnd_3059808 := by exact prefixLift 3059808
  have htrace : WordTrace (prefixWord ++ tailWord_3059808) baseStart_3059808 baseEnd_3059808 := by
    simpa [prefixWord, tailWord_3059808, baseEnd_3059808] using wordTrace_append hprefix tailTrace_3059808
  have hstable : (prefixWord ++ tailWord_3059808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059808).length < 2 ^ (prefixWord ++ tailWord_3059808).sum := by decide
  have hdescent : baseEnd_3059808 < baseStart_3059808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059851 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_3059851 : Nat := 118140960795 + 3059851 * 2 ^ 59
def prefixEnd_3059851 : Nat := 4983230072969 + 3 ^ 40 * 3059851 * 2
def baseEnd_3059851 : Nat := 1571174294140613052590507

theorem tailTrace_3059851 : CollatzResearch.WordTrace tailWord_3059851 prefixEnd_3059851 1571174294140613052590507 := by
  unfold tailWord_3059851
  simp only [CollatzResearch.WordTrace]
  refine ⟨111601934437689882791115407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74401289625126588527410271 111601934437689882791115407)
  ·
    refine ⟨167402901656534824186673111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111601934437689882791115407 167402901656534824186673111)
    ·
      refine ⟨251104352484802236280009667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167402901656534824186673111 251104352484802236280009667)
      ·
        refine ⟨376656528727203354420014501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251104352484802236280009667 376656528727203354420014501)
        ·
          refine ⟨70623099136350628953752719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376656528727203354420014501 70623099136350628953752719)
          ·
            refine ⟨105934648704525943430629079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70623099136350628953752719 105934648704525943430629079)
            ·
              refine ⟨158901973056788915145943619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105934648704525943430629079 158901973056788915145943619)
              ·
                refine ⟨238352959585183372718915429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158901973056788915145943619 238352959585183372718915429)
                ·
                  refine ⟨44691179922221882384796643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238352959585183372718915429 44691179922221882384796643)
                  ·
                    refine ⟨67036769883332823577194965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44691179922221882384796643 67036769883332823577194965)
                    ·
                      refine ⟨1571174294140613052590507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67036769883332823577194965 1571174294140613052590507)
                      ·
                        rfl

theorem cell23_3059851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_3059851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059851 prefixEnd_3059851 := by exact prefixLift 3059851
  have htrace : WordTrace (prefixWord ++ tailWord_3059851) baseStart_3059851 baseEnd_3059851 := by
    simpa [prefixWord, tailWord_3059851, baseEnd_3059851] using wordTrace_append hprefix tailTrace_3059851
  have hstable : (prefixWord ++ tailWord_3059851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059851).length < 2 ^ (prefixWord ++ tailWord_3059851).sum := by decide
  have hdescent : baseEnd_3059851 < baseStart_3059851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059912 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_3059912 : Nat := 118140960795 + 3059912 * 2 ^ 59
def prefixEnd_3059912 : Nat := 4983230072969 + 3 ^ 40 * 3059912 * 2
def baseEnd_3059912 : Nat := 1571205616460537313927727

theorem tailTrace_3059912 : CollatzResearch.WordTrace tailWord_3059912 prefixEnd_3059912 1571205616460537313927727 := by
  unfold tailWord_3059912
  simp only [CollatzResearch.WordTrace]
  refine ⟨55802079645234445104542995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74402772860312593472723993 55802079645234445104542995)
  ·
    refine ⟨83703119467851667656814493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55802079645234445104542995 83703119467851667656814493)
    ·
      refine ⟨31388669800444375371305435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83703119467851667656814493 31388669800444375371305435)
      ·
        refine ⟨47083004700666563056958153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31388669800444375371305435 47083004700666563056958153)
        ·
          refine ⟨35312253525499922292718615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47083004700666563056958153 35312253525499922292718615)
          ·
            refine ⟨52968380288249883439077923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35312253525499922292718615 52968380288249883439077923)
            ·
              refine ⟨79452570432374825158616885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52968380288249883439077923 79452570432374825158616885)
              ·
                refine ⟨7448678478035139858620333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79452570432374825158616885 7448678478035139858620333)
                ·
                  refine ⟨2793254429263177446982625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7448678478035139858620333 2793254429263177446982625)
                  ·
                    refine ⟨2094940821947383085236969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2793254429263177446982625 2094940821947383085236969)
                    ·
                      refine ⟨1571205616460537313927727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094940821947383085236969 1571205616460537313927727)
                      ·
                        rfl

theorem cell23_3059912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_3059912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059912 prefixEnd_3059912 := by exact prefixLift 3059912
  have htrace : WordTrace (prefixWord ++ tailWord_3059912) baseStart_3059912 baseEnd_3059912 := by
    simpa [prefixWord, tailWord_3059912, baseEnd_3059912] using wordTrace_append hprefix tailTrace_3059912
  have hstable : (prefixWord ++ tailWord_3059912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059912).length < 2 ^ (prefixWord ++ tailWord_3059912).sum := by decide
  have hdescent : baseEnd_3059912 < baseStart_3059912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059922 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3059922 : Nat := 118140960795 + 3059922 * 2 ^ 59
def prefixEnd_3059922 : Nat := 4983230072969 + 3 ^ 40 * 3059922 * 2
def baseEnd_3059922 : Nat := 523736917089027424934227

theorem tailTrace_3059922 : CollatzResearch.WordTrace tailWord_3059922 prefixEnd_3059922 523736917089027424934227 := by
  unfold tailWord_3059922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27901131005108165479237505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74403016013621774611300013 27901131005108165479237505)
  ·
    refine ⟨20925848253831124109428129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27901131005108165479237505 20925848253831124109428129)
    ·
      refine ⟨15694386190373343082071097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20925848253831124109428129 15694386190373343082071097)
      ·
        refine ⟨11770789642780007311553323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15694386190373343082071097 11770789642780007311553323)
        ·
          refine ⟨17656184464170010967329985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11770789642780007311553323 17656184464170010967329985)
          ·
            refine ⟨13242138348127508225497489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17656184464170010967329985 13242138348127508225497489)
            ·
              refine ⟨9931603761095631169123117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13242138348127508225497489 9931603761095631169123117)
              ·
                refine ⟨3724351410410861688421169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9931603761095631169123117 3724351410410861688421169)
                ·
                  refine ⟨2793263557808146266315877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3724351410410861688421169 2793263557808146266315877)
                  ·
                    refine ⟨523736917089027424934227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793263557808146266315877 523736917089027424934227)
                    ·
                      rfl

theorem cell23_3059922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3059922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059922 prefixEnd_3059922 := by exact prefixLift 3059922
  have htrace : WordTrace (prefixWord ++ tailWord_3059922) baseStart_3059922 baseEnd_3059922 := by
    simpa [prefixWord, tailWord_3059922, baseEnd_3059922] using wordTrace_append hprefix tailTrace_3059922
  have hstable : (prefixWord ++ tailWord_3059922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059922).length < 2 ^ (prefixWord ++ tailWord_3059922).sum := by decide
  have hdescent : baseEnd_3059922 < baseStart_3059922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059945 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_3059945 : Nat := 118140960795 + 3059945 * 2 ^ 59
def prefixEnd_3059945 : Nat := 4983230072969 + 3 ^ 40 * 3059945 * 2
def baseEnd_3059945 : Nat := 1571222561322135684815075

theorem tailTrace_3059945 : CollatzResearch.WordTrace tailWord_3059945 prefixEnd_3059945 1571222561322135684815075 := by
  unfold tailWord_3059945
  simp only [CollatzResearch.WordTrace]
  refine ⟨111605362899349336845037289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74403575266232891230024859 111605362899349336845037289)
  ·
    refine ⟨83704022174512002633777967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111605362899349336845037289 83704022174512002633777967)
    ·
      refine ⟨125556033261768003950666951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83704022174512002633777967 125556033261768003950666951)
      ·
        refine ⟨188334049892652005926000427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125556033261768003950666951 188334049892652005926000427)
        ·
          refine ⟨282501074838978008889000641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188334049892652005926000427 282501074838978008889000641)
          ·
            refine ⟨211875806129233506666750481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282501074838978008889000641 211875806129233506666750481)
            ·
              refine ⟨158906854596925130000062861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211875806129233506666750481 158906854596925130000062861)
              ·
                refine ⟨59590070473846923750023573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158906854596925130000062861 59590070473846923750023573)
                ·
                  refine ⟨2793284553461574550782355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59590070473846923750023573 2793284553461574550782355)
                  ·
                    refine ⟨4189926830192361826173533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793284553461574550782355 4189926830192361826173533)
                    ·
                      refine ⟨1571222561322135684815075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189926830192361826173533 1571222561322135684815075)
                      ·
                        rfl

theorem cell23_3059945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_3059945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059945 prefixEnd_3059945 := by exact prefixLift 3059945
  have htrace : WordTrace (prefixWord ++ tailWord_3059945) baseStart_3059945 baseEnd_3059945 := by
    simpa [prefixWord, tailWord_3059945, baseEnd_3059945] using wordTrace_append hprefix tailTrace_3059945
  have hstable : (prefixWord ++ tailWord_3059945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059945).length < 2 ^ (prefixWord ++ tailWord_3059945).sum := by decide
  have hdescent : baseEnd_3059945 < baseStart_3059945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059946 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_3059946 : Nat := 118140960795 + 3059946 * 2 ^ 59
def prefixEnd_3059946 : Nat := 4983230072969 + 3 ^ 40 * 3059946 * 2
def baseEnd_3059946 : Nat := 1571223074802790180902571

theorem tailTrace_3059946 : CollatzResearch.WordTrace tailWord_3059946 prefixEnd_3059946 1571223074802790180902571 := by
  unfold tailWord_3059946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27901349843086428503955923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74403599581563809343882461 27901349843086428503955923)
  ·
    refine ⟨41852024764629642755933885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27901349843086428503955923 41852024764629642755933885)
    ·
      refine ⟨15694509286736116033475207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41852024764629642755933885 15694509286736116033475207)
      ·
        refine ⟨23541763930104174050212811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15694509286736116033475207 23541763930104174050212811)
        ·
          refine ⟨35312645895156261075319217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23541763930104174050212811 35312645895156261075319217)
          ·
            refine ⟨26484484421367195806489413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35312645895156261075319217 26484484421367195806489413)
            ·
              refine ⟨4965840829006349213716765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26484484421367195806489413 4965840829006349213716765)
              ·
                refine ⟨1862190310877380955143787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4965840829006349213716765 1862190310877380955143787)
                ·
                  refine ⟨2793285466316071432715681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862190310877380955143787 2793285466316071432715681)
                  ·
                    refine ⟨2094964099737053574536761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2793285466316071432715681 2094964099737053574536761)
                    ·
                      refine ⟨1571223074802790180902571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2094964099737053574536761 1571223074802790180902571)
                      ·
                        rfl

theorem cell23_3059946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_3059946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059946 prefixEnd_3059946 := by exact prefixLift 3059946
  have htrace : WordTrace (prefixWord ++ tailWord_3059946) baseStart_3059946 baseEnd_3059946 := by
    simpa [prefixWord, tailWord_3059946, baseEnd_3059946] using wordTrace_append hprefix tailTrace_3059946
  have hstable : (prefixWord ++ tailWord_3059946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059946).length < 2 ^ (prefixWord ++ tailWord_3059946).sum := by decide
  have hdescent : baseEnd_3059946 < baseStart_3059946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059949 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3059949 : Nat := 118140960795 + 3059949 * 2 ^ 59
def prefixEnd_3059949 : Nat := 4983230072969 + 3 ^ 40 * 3059949 * 2
def baseEnd_3059949 : Nat := 1571224615244753669165057

theorem tailTrace_3059949 : CollatzResearch.WordTrace tailWord_3059949 prefixEnd_3059949 1571224615244753669165057 := by
  unfold tailWord_3059949
  simp only [CollatzResearch.WordTrace]
  refine ⟨111605508791334845528182901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74403672527556563685455267 111605508791334845528182901)
  ·
    refine ⟨10463016449187641768267147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111605508791334845528182901 10463016449187641768267147)
    ·
      refine ⟨15694524673781462652400721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463016449187641768267147 15694524673781462652400721)
      ·
        refine ⟨11770893505336096989300541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15694524673781462652400721 11770893505336096989300541)
        ·
          refine ⟨4414085064501036370987703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11770893505336096989300541 4414085064501036370987703)
          ·
            refine ⟨6621127596751554556481555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414085064501036370987703 6621127596751554556481555)
            ·
              refine ⟨9931691395127331834722333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621127596751554556481555 9931691395127331834722333)
              ·
                refine ⟨3724384273172749438020875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9931691395127331834722333 3724384273172749438020875)
                ·
                  refine ⟨5586576409759124157031313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724384273172749438020875 5586576409759124157031313)
                  ·
                    refine ⟨4189932307319343117773485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586576409759124157031313 4189932307319343117773485)
                    ·
                      refine ⟨1571224615244753669165057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189932307319343117773485 1571224615244753669165057)
                      ·
                        rfl

theorem cell23_3059949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3059949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059949 prefixEnd_3059949 := by exact prefixLift 3059949
  have htrace : WordTrace (prefixWord ++ tailWord_3059949) baseStart_3059949 baseEnd_3059949 := by
    simpa [prefixWord, tailWord_3059949, baseEnd_3059949] using wordTrace_append hprefix tailTrace_3059949
  have hstable : (prefixWord ++ tailWord_3059949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059949).length < 2 ^ (prefixWord ++ tailWord_3059949).sum := by decide
  have hdescent : baseEnd_3059949 < baseStart_3059949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059962 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_3059962 : Nat := 118140960795 + 3059962 * 2 ^ 59
def prefixEnd_3059962 : Nat := 4983230072969 + 3 ^ 40 * 3059962 * 2
def baseEnd_3059962 : Nat := 1571231290493262118302497

theorem tailTrace_3059962 : CollatzResearch.WordTrace tailWord_3059962 prefixEnd_3059962 1571231290493262118302497 := by
  unfold tailWord_3059962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27901495735071937187101535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74403988626858499165604093 27901495735071937187101535)
  ·
    refine ⟨41852243602607905780652303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27901495735071937187101535 41852243602607905780652303)
    ·
      refine ⟨62778365403911858670978455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41852243602607905780652303 62778365403911858670978455)
      ·
        refine ⟨94167548105867788006467683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62778365403911858670978455 94167548105867788006467683)
        ·
          refine ⟨141251322158801682009701525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94167548105867788006467683 141251322158801682009701525)
          ·
            refine ⟨6621155726193828844204759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141251322158801682009701525 6621155726193828844204759)
            ·
              refine ⟨9931733589290743266307139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621155726193828844204759 9931733589290743266307139)
              ·
                refine ⟨14897600383936114899460709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931733589290743266307139 14897600383936114899460709)
                ·
                  refine ⟨2793300071988021543648883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14897600383936114899460709 2793300071988021543648883)
                  ·
                    refine ⟨4189950107982032315473325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793300071988021543648883 4189950107982032315473325)
                    ·
                      refine ⟨1571231290493262118302497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189950107982032315473325 1571231290493262118302497)
                      ·
                        rfl

theorem cell23_3059962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_3059962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059962 prefixEnd_3059962 := by exact prefixLift 3059962
  have htrace : WordTrace (prefixWord ++ tailWord_3059962) baseStart_3059962 baseEnd_3059962 := by
    simpa [prefixWord, tailWord_3059962, baseEnd_3059962] using wordTrace_append hprefix tailTrace_3059962
  have hstable : (prefixWord ++ tailWord_3059962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059962).length < 2 ^ (prefixWord ++ tailWord_3059962).sum := by decide
  have hdescent : baseEnd_3059962 < baseStart_3059962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059968 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3059968 : Nat := 118140960795 + 3059968 * 2 ^ 59
def prefixEnd_3059968 : Nat := 4983230072969 + 3 ^ 40 * 3059968 * 2
def baseEnd_3059968 : Nat := 1571234371377189094827469

theorem tailTrace_3059968 : CollatzResearch.WordTrace tailWord_3059968 prefixEnd_3059968 1571234371377189094827469 := by
  unfold tailWord_3059968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55803100889133005886562279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74404134518844007848749705 55803100889133005886562279)
  ·
    refine ⟨83704651333699508829843419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55803100889133005886562279 83704651333699508829843419)
    ·
      refine ⟨125556977000549263244765129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83704651333699508829843419 125556977000549263244765129)
      ·
        refine ⟨94167732750411947433573847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125556977000549263244765129 94167732750411947433573847)
        ·
          refine ⟨141251599125617921150360771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94167732750411947433573847 141251599125617921150360771)
          ·
            refine ⟨211877398688426881725541157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141251599125617921150360771 211877398688426881725541157)
            ·
              refine ⟨39727012254080040323538967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211877398688426881725541157 39727012254080040323538967)
              ·
                refine ⟨59590518381120060485308451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39727012254080040323538967 59590518381120060485308451)
                ·
                  refine ⟨89385777571680090727962677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59590518381120060485308451 89385777571680090727962677)
                  ·
                    refine ⟨8379916647345008505746501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89385777571680090727962677 8379916647345008505746501)
                    ·
                      refine ⟨1571234371377189094827469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8379916647345008505746501 1571234371377189094827469)
                      ·
                        rfl

theorem cell23_3059968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3059968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059968 prefixEnd_3059968 := by exact prefixLift 3059968
  have htrace : WordTrace (prefixWord ++ tailWord_3059968) baseStart_3059968 baseEnd_3059968 := by
    simpa [prefixWord, tailWord_3059968, baseEnd_3059968] using wordTrace_append hprefix tailTrace_3059968
  have hstable : (prefixWord ++ tailWord_3059968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059968).length < 2 ^ (prefixWord ++ tailWord_3059968).sum := by decide
  have hdescent : baseEnd_3059968 < baseStart_3059968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3059979 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 2, 1, 3]
def baseStart_3059979 : Nat := 118140960795 + 3059979 * 2 ^ 59
def prefixEnd_3059979 : Nat := 4983230072969 + 3 ^ 40 * 3059979 * 2
def baseEnd_3059979 : Nat := 1571240019664388551789919

theorem tailTrace_3059979 : CollatzResearch.WordTrace tailWord_3059979 prefixEnd_3059979 1571240019664388551789919 := by
  unfold tailWord_3059979
  simp only [CollatzResearch.WordTrace]
  refine ⟨111606602981226160651774991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74404401987484107101183327 111606602981226160651774991)
  ·
    refine ⟨167409904471839240977662487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111606602981226160651774991 167409904471839240977662487)
    ·
      refine ⟨251114856707758861466493731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167409904471839240977662487 251114856707758861466493731)
      ·
        refine ⟨376672285061638292199740597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251114856707758861466493731 376672285061638292199740597)
        ·
          refine ⟨35313026724528589893725681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 376672285061638292199740597 35313026724528589893725681)
          ·
            refine ⟨26484770043396442420294261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35313026724528589893725681 26484770043396442420294261)
            ·
              refine ⟨2482947191568416476902587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26484770043396442420294261 2482947191568416476902587)
              ·
                refine ⟨3724420787352624715353881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482947191568416476902587 3724420787352624715353881)
                ·
                  refine ⟨2793315590514468536515411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3724420787352624715353881 2793315590514468536515411)
                  ·
                    refine ⟨4189973385771702804773117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793315590514468536515411 4189973385771702804773117)
                    ·
                      refine ⟨1571240019664388551789919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4189973385771702804773117 1571240019664388551789919)
                      ·
                        rfl

theorem cell23_3059979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 1, 3].length) (baseStart_3059979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3059979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3059979 prefixEnd_3059979 := by exact prefixLift 3059979
  have htrace : WordTrace (prefixWord ++ tailWord_3059979) baseStart_3059979 baseEnd_3059979 := by
    simpa [prefixWord, tailWord_3059979, baseEnd_3059979] using wordTrace_append hprefix tailTrace_3059979
  have hstable : (prefixWord ++ tailWord_3059979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3059979).length < 2 ^ (prefixWord ++ tailWord_3059979).sum := by decide
  have hdescent : baseEnd_3059979 < baseStart_3059979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3059979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060019 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 2, 2, 2]
def baseStart_3060019 : Nat := 118140960795 + 3060019 * 2 ^ 59
def prefixEnd_3060019 : Nat := 4983230072969 + 3 ^ 40 * 3060019 * 2
def baseEnd_3060019 : Nat := 1571260558890568395289735

theorem tailTrace_3060019 : CollatzResearch.WordTrace tailWord_3060019 prefixEnd_3060019 1571260558890568395289735 := by
  unfold tailWord_3060019
  simp only [CollatzResearch.WordTrace]
  refine ⟨111608061901081247483231111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74405374600720831655487407 111608061901081247483231111)
  ·
    refine ⟨167412092851621871224846667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111608061901081247483231111 167412092851621871224846667)
    ·
      refine ⟨251118139277432806837270001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167412092851621871224846667 251118139277432806837270001)
      ·
        refine ⟨188338604458074605127952501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251118139277432806837270001 188338604458074605127952501)
        ·
          refine ⟨17656744167944494230745547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188338604458074605127952501 17656744167944494230745547)
          ·
            refine ⟨26485116251916741346118321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17656744167944494230745547 26485116251916741346118321)
            ·
              refine ⟨19863837188937556009588741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26485116251916741346118321 19863837188937556009588741)
              ·
                refine ⟨3724469472925791751797889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19863837188937556009588741 3724469472925791751797889)
                ·
                  refine ⟨2793352104694343813848417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3724469472925791751797889 2793352104694343813848417)
                  ·
                    refine ⟨2095014078520757860386313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2793352104694343813848417 2095014078520757860386313)
                    ·
                      refine ⟨1571260558890568395289735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095014078520757860386313 1571260558890568395289735)
                      ·
                        rfl

theorem cell23_3060019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2, 2].length) (baseStart_3060019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060019 prefixEnd_3060019 := by exact prefixLift 3060019
  have htrace : WordTrace (prefixWord ++ tailWord_3060019) baseStart_3060019 baseEnd_3060019 := by
    simpa [prefixWord, tailWord_3060019, baseEnd_3060019] using wordTrace_append hprefix tailTrace_3060019
  have hstable : (prefixWord ++ tailWord_3060019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060019).length < 2 ^ (prefixWord ++ tailWord_3060019).sum := by decide
  have hdescent : baseEnd_3060019 < baseStart_3060019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060035 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3]
def baseStart_3060035 : Nat := 118140960795 + 3060035 * 2 ^ 59
def prefixEnd_3060035 : Nat := 4983230072969 + 3 ^ 40 * 3060035 * 2
def baseEnd_3060035 : Nat := 1571268774581040332689661

theorem tailTrace_3060035 : CollatzResearch.WordTrace tailWord_3060035 prefixEnd_3060035 1571268774581040332689661 := by
  unfold tailWord_3060035
  simp only [CollatzResearch.WordTrace]
  refine ⟨111608645469023282215813559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74405763646015521477209039 111608645469023282215813559)
  ·
    refine ⟨167412968203534923323720339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111608645469023282215813559 167412968203534923323720339)
    ·
      refine ⟨251119452305302384985580509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167412968203534923323720339 251119452305302384985580509)
      ·
        refine ⟨94169794614488394369592691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251119452305302384985580509 94169794614488394369592691)
        ·
          refine ⟨141254691921732591554389037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94169794614488394369592691 141254691921732591554389037)
          ·
            refine ⟨52970509470649721832895889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141254691921732591554389037 52970509470649721832895889)
            ·
              refine ⟨39727882102987291374671917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52970509470649721832895889 39727882102987291374671917)
              ·
                refine ⟨14897955788620234265501969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39727882102987291374671917 14897955788620234265501969)
                ·
                  refine ⟨11173466841465175699126477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14897955788620234265501969 11173466841465175699126477)
                  ·
                    refine ⟨4190050065549440887172429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11173466841465175699126477 4190050065549440887172429)
                    ·
                      refine ⟨1571268774581040332689661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190050065549440887172429 1571268774581040332689661)
                      ·
                        rfl

theorem cell23_3060035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_3060035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060035 prefixEnd_3060035 := by exact prefixLift 3060035
  have htrace : WordTrace (prefixWord ++ tailWord_3060035) baseStart_3060035 baseEnd_3060035 := by
    simpa [prefixWord, tailWord_3060035, baseEnd_3060035] using wordTrace_append hprefix tailTrace_3060035
  have hstable : (prefixWord ++ tailWord_3060035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060035).length < 2 ^ (prefixWord ++ tailWord_3060035).sum := by decide
  have hdescent : baseEnd_3060035 < baseStart_3060035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060072 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3060072 : Nat := 118140960795 + 3060072 * 2 ^ 59
def prefixEnd_3060072 : Nat := 4983230072969 + 3 ^ 40 * 3060072 * 2
def baseEnd_3060072 : Nat := 523762591121752229308997

theorem tailTrace_3060072 : CollatzResearch.WordTrace tailWord_3060072 prefixEnd_3060072 523762591121752229308997 := by
  unfold tailWord_3060072
  simp only [CollatzResearch.WordTrace]
  refine ⟨55804997484944618767455235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74406663313259491689940313 55804997484944618767455235)
  ·
    refine ⟨83707496227416928151182853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55804997484944618767455235 83707496227416928151182853)
    ·
      refine ⟨15695155542640674028346785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83707496227416928151182853 15695155542640674028346785)
      ·
        refine ⟨11771366656980505521260089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15695155542640674028346785 11771366656980505521260089)
        ·
          refine ⟨8828524992735379140945067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11771366656980505521260089 8828524992735379140945067)
          ·
            refine ⟨13242787489103068711417601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828524992735379140945067 13242787489103068711417601)
            ·
              refine ⟨9932090616827301533563201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13242787489103068711417601 9932090616827301533563201)
              ·
                refine ⟨7449067962620476150172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9932090616827301533563201 7449067962620476150172401)
                ·
                  refine ⟨5586800971965357112629301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449067962620476150172401 5586800971965357112629301)
                  ·
                    refine ⟨523762591121752229308997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5586800971965357112629301 523762591121752229308997)
                    ·
                      rfl

theorem cell23_3060072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3060072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060072 prefixEnd_3060072 := by exact prefixLift 3060072
  have htrace : WordTrace (prefixWord ++ tailWord_3060072) baseStart_3060072 baseEnd_3060072 := by
    simpa [prefixWord, tailWord_3060072, baseEnd_3060072] using wordTrace_append hprefix tailTrace_3060072
  have hstable : (prefixWord ++ tailWord_3060072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060072).length < 2 ^ (prefixWord ++ tailWord_3060072).sum := by decide
  have hdescent : baseEnd_3060072 < baseStart_3060072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060076 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 5]
def baseStart_3060076 : Nat := 118140960795 + 3060076 * 2 ^ 59
def prefixEnd_3060076 : Nat := 4983230072969 + 3 ^ 40 * 3060076 * 2
def baseEnd_3060076 : Nat := 174587758587541630252997

theorem tailTrace_3060076 : CollatzResearch.WordTrace tailWord_3060076 prefixEnd_3060076 174587758587541630252997 := by
  unfold tailWord_3060076
  simp only [CollatzResearch.WordTrace]
  refine ⟨55805070430937373109028041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74406760574583164145370721 55805070430937373109028041)
  ·
    refine ⟨41853802823203029831771031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55805070430937373109028041 41853802823203029831771031)
    ·
      refine ⟨62780704234804544747656547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41853802823203029831771031 62780704234804544747656547)
      ·
        refine ⟨94171056352206817121484821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62780704234804544747656547 94171056352206817121484821)
        ·
          refine ⟨4414268266509694552569601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94171056352206817121484821 4414268266509694552569601)
          ·
            refine ⟨3310701199882270914427201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414268266509694552569601 3310701199882270914427201)
            ·
              refine ⟨2483025899911703185820401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3310701199882270914427201 2483025899911703185820401)
              ·
                refine ⟨1862269424933777389365301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483025899911703185820401 1862269424933777389365301)
                ·
                  refine ⟨174587758587541630252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1862269424933777389365301 174587758587541630252997)
                  ·
                    rfl

theorem cell23_3060076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_3060076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060076 prefixEnd_3060076 := by exact prefixLift 3060076
  have htrace : WordTrace (prefixWord ++ tailWord_3060076) baseStart_3060076 baseEnd_3060076 := by
    simpa [prefixWord, tailWord_3060076, baseEnd_3060076] using wordTrace_append hprefix tailTrace_3060076
  have hstable : (prefixWord ++ tailWord_3060076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060076).length < 2 ^ (prefixWord ++ tailWord_3060076).sum := by decide
  have hdescent : baseEnd_3060076 < baseStart_3060076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060086 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3060086 : Nat := 118140960795 + 3060086 * 2 ^ 59
def prefixEnd_3060086 : Nat := 4983230072969 + 3 ^ 40 * 3060086 * 2
def baseEnd_3060086 : Nat := 1571294962094419633151927

theorem tailTrace_3060086 : CollatzResearch.WordTrace tailWord_3060086 prefixEnd_3060086 1571294962094419633151927 := by
  unfold tailWord_3060086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975656599489907370370007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74407003727892345283946741 6975656599489907370370007)
  ·
    refine ⟨10463484899234861055555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975656599489907370370007 10463484899234861055555011)
    ·
      refine ⟨15695227348852291583332517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463484899234861055555011 15695227348852291583332517)
      ·
        refine ⟨2942855127909804671874847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15695227348852291583332517 2942855127909804671874847)
        ·
          refine ⟨4414282691864707007812271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942855127909804671874847 4414282691864707007812271)
          ·
            refine ⟨6621424037797060511718407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414282691864707007812271 6621424037797060511718407)
            ·
              refine ⟨9932136056695590767577611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621424037797060511718407 9932136056695590767577611)
              ·
                refine ⟨14898204085043386151366417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932136056695590767577611 14898204085043386151366417)
                ·
                  refine ⟨11173653063782539613524813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14898204085043386151366417 11173653063782539613524813)
                  ·
                    refine ⟨4190119898918452355071805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11173653063782539613524813 4190119898918452355071805)
                    ·
                      refine ⟨1571294962094419633151927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190119898918452355071805 1571294962094419633151927)
                      ·
                        rfl

theorem cell23_3060086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3060086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060086 prefixEnd_3060086 := by exact prefixLift 3060086
  have htrace : WordTrace (prefixWord ++ tailWord_3060086) baseStart_3060086 baseEnd_3060086 := by
    simpa [prefixWord, tailWord_3060086, baseEnd_3060086] using wordTrace_append hprefix tailTrace_3060086
  have hstable : (prefixWord ++ tailWord_3060086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060086).length < 2 ^ (prefixWord ++ tailWord_3060086).sum := by decide
  have hdescent : baseEnd_3060086 < baseStart_3060086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060095 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_3060095 : Nat := 118140960795 + 3060095 * 2 ^ 59
def prefixEnd_3060095 : Nat := 4983230072969 + 3 ^ 40 * 3060095 * 2
def baseEnd_3060095 : Nat := 1571299583420310097939385

theorem tailTrace_3060095 : CollatzResearch.WordTrace tailWord_3060095 prefixEnd_3060095 1571299583420310097939385 := by
  unfold tailWord_3060095
  simp only [CollatzResearch.WordTrace]
  refine ⟨111610833848805912462997739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74407222565870608308665159 111610833848805912462997739)
  ·
    refine ⟨167416250773208868694496609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111610833848805912462997739 167416250773208868694496609)
    ·
      refine ⟨125562188079906651520872457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167416250773208868694496609 125562188079906651520872457)
      ·
        refine ⟨94171641059929988640654343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125562188079906651520872457 94171641059929988640654343)
        ·
          refine ⟨141257461589894982960981515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94171641059929988640654343 141257461589894982960981515)
          ·
            refine ⟨211886192384842474441472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141257461589894982960981515 211886192384842474441472273)
            ·
              refine ⟨158914644288631855831104205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211886192384842474441472273 158914644288631855831104205)
              ·
                refine ⟨59592991608236945936664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158914644288631855831104205 59592991608236945936664077)
                ·
                  refine ⟨22347371853088854726249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59592991608236945936664077 22347371853088854726249029)
                  ·
                    refine ⟨4190132222454160261171693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22347371853088854726249029 4190132222454160261171693)
                    ·
                      refine ⟨1571299583420310097939385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190132222454160261171693 1571299583420310097939385)
                      ·
                        rfl

theorem cell23_3060095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_3060095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060095 prefixEnd_3060095 := by exact prefixLift 3060095
  have htrace : WordTrace (prefixWord ++ tailWord_3060095) baseStart_3060095 baseEnd_3060095 := by
    simpa [prefixWord, tailWord_3060095, baseEnd_3060095] using wordTrace_append hprefix tailTrace_3060095
  have hstable : (prefixWord ++ tailWord_3060095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060095).length < 2 ^ (prefixWord ++ tailWord_3060095).sum := by decide
  have hdescent : baseEnd_3060095 < baseStart_3060095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060106 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3060106 : Nat := 118140960795 + 3060106 * 2 ^ 59
def prefixEnd_3060106 : Nat := 4983230072969 + 3 ^ 40 * 3060106 * 2
def baseEnd_3060106 : Nat := 523768410569169851633945

theorem tailTrace_3060106 : CollatzResearch.WordTrace tailWord_3060106 prefixEnd_3060106 523768410569169851633945 := by
  unfold tailWord_3060106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27902808762941515335412043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74407490034510707561098781 27902808762941515335412043)
  ·
    refine ⟨41854213144412273003118065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27902808762941515335412043 41854213144412273003118065)
    ·
      refine ⟨31390659858309204752338549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41854213144412273003118065 31390659858309204752338549)
      ·
        refine ⟨2942874361716487945531739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31390659858309204752338549 2942874361716487945531739)
        ·
          refine ⟨4414311542574731918297609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942874361716487945531739 4414311542574731918297609)
          ·
            refine ⟨3310733656931048938723207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414311542574731918297609 3310733656931048938723207)
            ·
              refine ⟨4966100485396573408084811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310733656931048938723207 4966100485396573408084811)
              ·
                refine ⟨7449150728094860112127217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966100485396573408084811 7449150728094860112127217)
                ·
                  refine ⟨5586863046071145084095413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449150728094860112127217 5586863046071145084095413)
                  ·
                    refine ⟨523768410569169851633945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5586863046071145084095413 523768410569169851633945)
                    ·
                      rfl

theorem cell23_3060106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3060106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060106 prefixEnd_3060106 := by exact prefixLift 3060106
  have htrace : WordTrace (prefixWord ++ tailWord_3060106) baseStart_3060106 baseEnd_3060106 := by
    simpa [prefixWord, tailWord_3060106, baseEnd_3060106] using wordTrace_append hprefix tailTrace_3060106
  have hstable : (prefixWord ++ tailWord_3060106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060106).length < 2 ^ (prefixWord ++ tailWord_3060106).sum := by decide
  have hdescent : baseEnd_3060106 < baseStart_3060106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060119 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 1, 4]
def baseStart_3060119 : Nat := 118140960795 + 3060119 * 2 ^ 59
def prefixEnd_3060119 : Nat := 4983230072969 + 3 ^ 40 * 3060119 * 2
def baseEnd_3060119 : Nat := 523770635652006001346425

theorem tailTrace_3060119 : CollatzResearch.WordTrace tailWord_3060119 prefixEnd_3060119 523770635652006001346425 := by
  unfold tailWord_3060119
  simp only [CollatzResearch.WordTrace]
  refine ⟨111611709200718964561871411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74407806133812643041247607 111611709200718964561871411)
  ·
    refine ⟨167417563801078446842807117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111611709200718964561871411 167417563801078446842807117)
    ·
      refine ⟨62781586425404417566052669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167417563801078446842807117 62781586425404417566052669)
      ·
        refine ⟨23543094909526656587269751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62781586425404417566052669 23543094909526656587269751)
        ·
          refine ⟨35314642364289984880904627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23543094909526656587269751 35314642364289984880904627)
          ·
            refine ⟨52971963546434977321356941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35314642364289984880904627 52971963546434977321356941)
            ·
              refine ⟨19864486329913116495508853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52971963546434977321356941 19864486329913116495508853)
              ·
                refine ⟨1862295593429354671453955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19864486329913116495508853 1862295593429354671453955)
                ·
                  refine ⟨2793443390144032007180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862295593429354671453955 2793443390144032007180933)
                  ·
                    refine ⟨523770635652006001346425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793443390144032007180933 523770635652006001346425)
                    ·
                      rfl

theorem cell23_3060119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_3060119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060119 prefixEnd_3060119 := by exact prefixLift 3060119
  have htrace : WordTrace (prefixWord ++ tailWord_3060119) baseStart_3060119 baseEnd_3060119 := by
    simpa [prefixWord, tailWord_3060119, baseEnd_3060119] using wordTrace_append hprefix tailTrace_3060119
  have hstable : (prefixWord ++ tailWord_3060119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060119).length < 2 ^ (prefixWord ++ tailWord_3060119).sum := by decide
  have hdescent : baseEnd_3060119 < baseStart_3060119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060126 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3060126 : Nat := 118140960795 + 3060126 * 2 ^ 59
def prefixEnd_3060126 : Nat := 4983230072969 + 3 ^ 40 * 3060126 * 2
def baseEnd_3060126 : Nat := 1571315501320599476651743

theorem tailTrace_3060126 : CollatzResearch.WordTrace tailWord_3060126 prefixEnd_3060126 1571315501320599476651743 := by
  unfold tailWord_3060126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951495563961700594672029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74407976341129069838250821 13951495563961700594672029)
  ·
    refine ⟨5231810836485637723002011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13951495563961700594672029 5231810836485637723002011)
    ·
      refine ⟨7847716254728456584503017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231810836485637723002011 7847716254728456584503017)
      ·
        refine ⟨5885787191046342438377263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7847716254728456584503017 5885787191046342438377263)
        ·
          refine ⟨8828680786569513657565895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885787191046342438377263 8828680786569513657565895)
          ·
            refine ⟨13243021179854270486348843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828680786569513657565895 13243021179854270486348843)
            ·
              refine ⟨19864531769781405729523265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243021179854270486348843 19864531769781405729523265)
              ·
                refine ⟨14898398827336054297142449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19864531769781405729523265 14898398827336054297142449)
                ·
                  refine ⟨11173799120502040722856837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14898398827336054297142449 11173799120502040722856837)
                  ·
                    refine ⟨2095087335094132635535657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11173799120502040722856837 2095087335094132635535657)
                    ·
                      refine ⟨1571315501320599476651743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095087335094132635535657 1571315501320599476651743)
                      ·
                        rfl

theorem cell23_3060126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3060126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060126 prefixEnd_3060126 := by exact prefixLift 3060126
  have htrace : WordTrace (prefixWord ++ tailWord_3060126) baseStart_3060126 baseEnd_3060126 := by
    simpa [prefixWord, tailWord_3060126, baseEnd_3060126] using wordTrace_append hprefix tailTrace_3060126
  have hstable : (prefixWord ++ tailWord_3060126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060126).length < 2 ^ (prefixWord ++ tailWord_3060126).sum := by decide
  have hdescent : baseEnd_3060126 < baseStart_3060126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060132 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 6]
def baseStart_3060132 : Nat := 118140960795 + 3060132 * 2 ^ 59
def prefixEnd_3060132 : Nat := 4983230072969 + 3 ^ 40 * 3060132 * 2
def baseEnd_3060132 : Nat := 174590953578280717019635

theorem tailTrace_3060132 : CollatzResearch.WordTrace tailWord_3060132 prefixEnd_3060132 174590953578280717019635 := by
  unfold tailWord_3060132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806091674835933891047325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74408122233114578521396433 55806091674835933891047325)
  ·
    refine ⟨20927284378063475209142747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55806091674835933891047325 20927284378063475209142747)
    ·
      refine ⟨31390926567095212813714121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20927284378063475209142747 31390926567095212813714121)
      ·
        refine ⟨23543194925321409610285591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31390926567095212813714121 23543194925321409610285591)
        ·
          refine ⟨35314792387982114415428387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23543194925321409610285591 35314792387982114415428387)
          ·
            refine ⟨52972188581973171623142581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35314792387982114415428387 52972188581973171623142581)
            ·
              refine ⟨4966142679559984839669617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52972188581973171623142581 4966142679559984839669617)
              ·
                refine ⟨3724607009669988629752213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966142679559984839669617 3724607009669988629752213)
                ·
                  refine ⟨174590953578280717019635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3724607009669988629752213 174590953578280717019635)
                  ·
                    rfl

theorem cell23_3060132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_3060132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060132 prefixEnd_3060132 := by exact prefixLift 3060132
  have htrace : WordTrace (prefixWord ++ tailWord_3060132) baseStart_3060132 baseEnd_3060132 := by
    simpa [prefixWord, tailWord_3060132, baseEnd_3060132] using wordTrace_append hprefix tailTrace_3060132
  have hstable : (prefixWord ++ tailWord_3060132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060132).length < 2 ^ (prefixWord ++ tailWord_3060132).sum := by decide
  have hdescent : baseEnd_3060132 < baseStart_3060132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060136 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3060136 : Nat := 118140960795 + 3060136 * 2 ^ 59
def prefixEnd_3060136 : Nat := 4983230072969 + 3 ^ 40 * 3060136 * 2
def baseEnd_3060136 : Nat := 523773545375714812508899

theorem tailTrace_3060136 : CollatzResearch.WordTrace tailWord_3060136 prefixEnd_3060136 523773545375714812508899 := by
  unfold tailWord_3060136
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806164620828688232620131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74408219494438250976826841 55806164620828688232620131)
  ·
    refine ⟨83709246931243032348930197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55806164620828688232620131 83709246931243032348930197)
    ·
      refine ⟨3923870949902017141356103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83709246931243032348930197 3923870949902017141356103)
      ·
        refine ⟨5885806424853025712034155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923870949902017141356103 5885806424853025712034155)
        ·
          refine ⟨8828709637279538568051233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885806424853025712034155 8828709637279538568051233)
          ·
            refine ⟨6621532227959653926038425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828709637279538568051233 6621532227959653926038425)
            ·
              refine ⟨4966149170969740444528819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621532227959653926038425 4966149170969740444528819)
              ·
                refine ⟨7449223756454610666793229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966149170969740444528819 7449223756454610666793229)
                ·
                  refine ⟨2793458908670479000047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7449223756454610666793229 2793458908670479000047461)
                  ·
                    refine ⟨523773545375714812508899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793458908670479000047461 523773545375714812508899)
                    ·
                      rfl

theorem cell23_3060136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3060136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060136 prefixEnd_3060136 := by exact prefixLift 3060136
  have htrace : WordTrace (prefixWord ++ tailWord_3060136) baseStart_3060136 baseEnd_3060136 := by
    simpa [prefixWord, tailWord_3060136, baseEnd_3060136] using wordTrace_append hprefix tailTrace_3060136
  have hstable : (prefixWord ++ tailWord_3060136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060136).length < 2 ^ (prefixWord ++ tailWord_3060136).sum := by decide
  have hdescent : baseEnd_3060136 < baseStart_3060136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060165 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_3060165 : Nat := 118140960795 + 3060165 * 2 ^ 59
def prefixEnd_3060165 : Nat := 4983230072969 + 3 ^ 40 * 3060165 * 2
def baseEnd_3060165 : Nat := 1571335527066124824064063

theorem tailTrace_3060165 : CollatzResearch.WordTrace tailWord_3060165 prefixEnd_3060165 1571335527066124824064063 := by
  unfold tailWord_3060165
  simp only [CollatzResearch.WordTrace]
  refine ⟨111613386958552314418045949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74408924639034876278697299 111613386958552314418045949)
  ·
    refine ⟨41855020109457117906767231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111613386958552314418045949 41855020109457117906767231)
    ·
      refine ⟨62782530164185676860150847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41855020109457117906767231 62782530164185676860150847)
      ·
        refine ⟨94173795246278515290226271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62782530164185676860150847 94173795246278515290226271)
        ·
          refine ⟨141260692869417772935339407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94173795246278515290226271 141260692869417772935339407)
          ·
            refine ⟨211891039304126659403009111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141260692869417772935339407 211891039304126659403009111)
            ·
              refine ⟨317836558956189989104513667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211891039304126659403009111 317836558956189989104513667)
              ·
                refine ⟨476754838434284983656770501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317836558956189989104513667 476754838434284983656770501)
                ·
                  refine ⟨89391532206428434435644469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476754838434284983656770501 89391532206428434435644469)
                  ·
                    refine ⟨8380456144352665728341669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89391532206428434435644469 8380456144352665728341669)
                    ·
                      refine ⟨1571335527066124824064063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8380456144352665728341669 1571335527066124824064063)
                      ·
                        rfl

theorem cell23_3060165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_3060165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060165 prefixEnd_3060165 := by exact prefixLift 3060165
  have htrace : WordTrace (prefixWord ++ tailWord_3060165) baseStart_3060165 baseEnd_3060165 := by
    simpa [prefixWord, tailWord_3060165, baseEnd_3060165] using wordTrace_append hprefix tailTrace_3060165
  have hstable : (prefixWord ++ tailWord_3060165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060165).length < 2 ^ (prefixWord ++ tailWord_3060165).sum := by decide
  have hdescent : baseEnd_3060165 < baseStart_3060165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060175 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 6]
def baseStart_3060175 : Nat := 118140960795 + 3060175 * 2 ^ 59
def prefixEnd_3060175 : Nat := 4983230072969 + 3 ^ 40 * 3060175 * 2
def baseEnd_3060175 : Nat := 523780220624223261646339

theorem tailTrace_3060175 : CollatzResearch.WordTrace tailWord_3060175 prefixEnd_3060175 523780220624223261646339 := by
  unfold tailWord_3060175
  simp only [CollatzResearch.WordTrace]
  refine ⟨111613751688516086125909979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74409167792344057417273319 111613751688516086125909979)
  ·
    refine ⟨167420627532774129188864969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111613751688516086125909979 167420627532774129188864969)
    ·
      refine ⟨125565470649580596891648727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167420627532774129188864969 125565470649580596891648727)
      ·
        refine ⟨188348205974370895337473091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125565470649580596891648727 188348205974370895337473091)
        ·
          refine ⟨282522308961556343006209637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188348205974370895337473091 282522308961556343006209637)
          ·
            refine ⟨52972932930291814313664307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282522308961556343006209637 52972932930291814313664307)
            ·
              refine ⟨79459399395437721470496461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52972932930291814313664307 79459399395437721470496461)
              ·
                refine ⟨29797274773289145551436173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79459399395437721470496461 29797274773289145551436173)
                ·
                  refine ⟨11173978039983429581788565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29797274773289145551436173 11173978039983429581788565)
                  ·
                    refine ⟨523780220624223261646339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11173978039983429581788565 523780220624223261646339)
                    ·
                      rfl

theorem cell23_3060175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_3060175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060175 prefixEnd_3060175 := by exact prefixLift 3060175
  have htrace : WordTrace (prefixWord ++ tailWord_3060175) baseStart_3060175 baseEnd_3060175 := by
    simpa [prefixWord, tailWord_3060175, baseEnd_3060175] using wordTrace_append hprefix tailTrace_3060175
  have hstable : (prefixWord ++ tailWord_3060175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060175).length < 2 ^ (prefixWord ++ tailWord_3060175).sum := by decide
  have hdescent : baseEnd_3060175 < baseStart_3060175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060192 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_3060192 : Nat := 118140960795 + 3060192 * 2 ^ 59
def prefixEnd_3060192 : Nat := 4983230072969 + 3 ^ 40 * 3060192 * 2
def baseEnd_3060192 : Nat := 523783130347932072808813

theorem tailTrace_3060192 : CollatzResearch.WordTrace tailWord_3060192 prefixEnd_3060192 523783130347932072808813 := by
  unfold tailWord_3060192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55807185864727249014639415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74409581152969665352852553 55807185864727249014639415)
  ·
    refine ⟨83710778797090873521959123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55807185864727249014639415 83710778797090873521959123)
    ·
      refine ⟨125566168195636310282938685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83710778797090873521959123 125566168195636310282938685)
      ·
        refine ⟨47087313073363616356102007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125566168195636310282938685 47087313073363616356102007)
        ·
          refine ⟨70630969610045424534153011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47087313073363616356102007 70630969610045424534153011)
          ·
            refine ⟨105946454415068136801229517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70630969610045424534153011 105946454415068136801229517)
            ·
              refine ⟨39729920405650551300461069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105946454415068136801229517 39729920405650551300461069)
              ·
                refine ⟨14898720152118956737672901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39729920405650551300461069 14898720152118956737672901)
                ·
                  refine ⟨2793510028522304388313669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14898720152118956737672901 2793510028522304388313669)
                  ·
                    refine ⟨523783130347932072808813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793510028522304388313669 523783130347932072808813)
                    ·
                      rfl

theorem cell23_3060192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_3060192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060192 prefixEnd_3060192 := by exact prefixLift 3060192
  have htrace : WordTrace (prefixWord ++ tailWord_3060192) baseStart_3060192 baseEnd_3060192 := by
    simpa [prefixWord, tailWord_3060192, baseEnd_3060192] using wordTrace_append hprefix tailTrace_3060192
  have hstable : (prefixWord ++ tailWord_3060192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060192).length < 2 ^ (prefixWord ++ tailWord_3060192).sum := by decide
  have hdescent : baseEnd_3060192 < baseStart_3060192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060193 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_3060193 : Nat := 118140960795 + 3060193 * 2 ^ 59
def prefixEnd_3060193 : Nat := 4983230072969 + 3 ^ 40 * 3060193 * 2
def baseEnd_3060193 : Nat := 1571349904524450714513935

theorem tailTrace_3060193 : CollatzResearch.WordTrace tailWord_3060193 prefixEnd_3060193 1571349904524450714513935 := by
  unfold tailWord_3060193
  simp only [CollatzResearch.WordTrace]
  refine ⟨111614408202450875200065233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74409605468300583466710155 111614408202450875200065233)
  ·
    refine ⟨83710806151838156400048925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111614408202450875200065233 83710806151838156400048925)
    ·
      refine ⟨31391552306939308650018347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83710806151838156400048925 31391552306939308650018347)
      ·
        refine ⟨47087328460408962975027521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31391552306939308650018347 47087328460408962975027521)
        ·
          refine ⟨35315496345306722231270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47087328460408962975027521 35315496345306722231270641)
          ·
            refine ⟨26486622258980041673452981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35315496345306722231270641 26486622258980041673452981)
            ·
              refine ⟨2483120836779378906886217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26486622258980041673452981 2483120836779378906886217)
              ·
                refine ⟨1862340627584534180164663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483120836779378906886217 1862340627584534180164663)
                ·
                  refine ⟨2793510941376801270246995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862340627584534180164663 2793510941376801270246995)
                  ·
                    refine ⟨4190266412065201905370493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793510941376801270246995 4190266412065201905370493)
                    ·
                      refine ⟨1571349904524450714513935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190266412065201905370493 1571349904524450714513935)
                      ·
                        rfl

theorem cell23_3060193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_3060193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060193 prefixEnd_3060193 := by exact prefixLift 3060193
  have htrace : WordTrace (prefixWord ++ tailWord_3060193) baseStart_3060193 baseEnd_3060193 := by
    simpa [prefixWord, tailWord_3060193, baseEnd_3060193] using wordTrace_append hprefix tailTrace_3060193
  have hstable : (prefixWord ++ tailWord_3060193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060193).length < 2 ^ (prefixWord ++ tailWord_3060193).sum := by decide
  have hdescent : baseEnd_3060193 < baseStart_3060193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060209 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_3060209 : Nat := 118140960795 + 3060209 * 2 ^ 59
def prefixEnd_3060209 : Nat := 4983230072969 + 3 ^ 40 * 3060209 * 2
def baseEnd_3060209 : Nat := 523786040071640883971287

theorem tailTrace_3060209 : CollatzResearch.WordTrace tailWord_3060209 prefixEnd_3060209 523786040071640883971287 := by
  unfold tailWord_3060209
  simp only [CollatzResearch.WordTrace]
  refine ⟨111614991770392909932647681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74409994513595273288431787 111614991770392909932647681)
  ·
    refine ⟨83711243827794682449485761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111614991770392909932647681 83711243827794682449485761)
    ·
      refine ⟨62783432870846011837114321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83711243827794682449485761 62783432870846011837114321)
      ·
        refine ⟨47087574653134508877835741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62783432870846011837114321 47087574653134508877835741)
        ·
          refine ⟨17657840494925440829188403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47087574653134508877835741 17657840494925440829188403)
          ·
            refine ⟨26486760742388161243782605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17657840494925440829188403 26486760742388161243782605)
            ·
              refine ⟨9932535278395560466418477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26486760742388161243782605 9932535278395560466418477)
              ·
                refine ⟨3724700729398335174906929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932535278395560466418477 3724700729398335174906929)
                ·
                  refine ⟨2793525547048751381180197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3724700729398335174906929 2793525547048751381180197)
                  ·
                    refine ⟨523786040071640883971287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793525547048751381180197 523786040071640883971287)
                    ·
                      rfl

theorem cell23_3060209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_3060209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060209 prefixEnd_3060209 := by exact prefixLift 3060209
  have htrace : WordTrace (prefixWord ++ tailWord_3060209) baseStart_3060209 baseEnd_3060209 := by
    simpa [prefixWord, tailWord_3060209, baseEnd_3060209] using wordTrace_append hprefix tailTrace_3060209
  have hstable : (prefixWord ++ tailWord_3060209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060209).length < 2 ^ (prefixWord ++ tailWord_3060209).sum := by decide
  have hdescent : baseEnd_3060209 < baseStart_3060209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060213 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3060213 : Nat := 118140960795 + 3060213 * 2 ^ 59
def prefixEnd_3060213 : Nat := 4983230072969 + 3 ^ 40 * 3060213 * 2
def baseEnd_3060213 : Nat := 523786724712513545421281

theorem tailTrace_3060213 : CollatzResearch.WordTrace tailWord_3060213 prefixEnd_3060213 523786724712513545421281 := by
  unfold tailWord_3060213
  simp only [CollatzResearch.WordTrace]
  refine ⟨111615137662378418615793293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74410091774918945743862195 111615137662378418615793293)
  ·
    refine ⟨41855676623391906980922485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111615137662378418615793293 41855676623391906980922485)
    ·
      refine ⟨3923969683442991279461483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41855676623391906980922485 3923969683442991279461483)
      ·
        refine ⟨5885954525164486919192225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923969683442991279461483 5885954525164486919192225)
        ·
          refine ⟨4414465893873365189394169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885954525164486919192225 4414465893873365189394169)
          ·
            refine ⟨3310849420405023892045627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414465893873365189394169 3310849420405023892045627)
            ·
              refine ⟨4966274130607535838068441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310849420405023892045627 4966274130607535838068441)
              ·
                refine ⟨3724705597955651878551331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966274130607535838068441 3724705597955651878551331)
                ·
                  refine ⟨5587058396933477817826997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724705597955651878551331 5587058396933477817826997)
                  ·
                    refine ⟨523786724712513545421281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5587058396933477817826997 523786724712513545421281)
                    ·
                      rfl

theorem cell23_3060213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3060213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060213 prefixEnd_3060213 := by exact prefixLift 3060213
  have htrace : WordTrace (prefixWord ++ tailWord_3060213) baseStart_3060213 baseEnd_3060213 := by
    simpa [prefixWord, tailWord_3060213, baseEnd_3060213] using wordTrace_append hprefix tailTrace_3060213
  have hstable : (prefixWord ++ tailWord_3060213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060213).length < 2 ^ (prefixWord ++ tailWord_3060213).sum := by decide
  have hdescent : baseEnd_3060213 < baseStart_3060213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060226 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3060226 : Nat := 118140960795 + 3060226 * 2 ^ 59
def prefixEnd_3060226 : Nat := 4983230072969 + 3 ^ 40 * 3060226 * 2
def baseEnd_3060226 : Nat := 523788949795349695133761

theorem tailTrace_3060226 : CollatzResearch.WordTrace tailWord_3060226 prefixEnd_3060226 523788949795349695133761 := by
  unfold tailWord_3060226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27903902952832830459004133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74410407874220881224011021 27903902952832830459004133)
  ·
    refine ⟨5231981803656155711063275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27903902952832830459004133 5231981803656155711063275)
    ·
      refine ⟨7847972705484233566594913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231981803656155711063275 7847972705484233566594913)
      ·
        refine ⟨5885979529113175174946185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7847972705484233566594913 5885979529113175174946185)
        ·
          refine ⟨4414484646834881381209639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885979529113175174946185 4414484646834881381209639)
          ·
            refine ⟨6621726970252322071814459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414484646834881381209639 6621726970252322071814459)
            ·
              refine ⟨9932590455378483107721689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621726970252322071814459 9932590455378483107721689)
              ·
                refine ⟨7449442841533862330791267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9932590455378483107721689 7449442841533862330791267)
                ·
                  refine ⟨11174164262300793496186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449442841533862330791267 11174164262300793496186901)
                  ·
                    refine ⟨523788949795349695133761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11174164262300793496186901 523788949795349695133761)
                    ·
                      rfl

theorem cell23_3060226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3060226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060226 prefixEnd_3060226 := by exact prefixLift 3060226
  have htrace : WordTrace (prefixWord ++ tailWord_3060226) baseStart_3060226 baseEnd_3060226 := by
    simpa [prefixWord, tailWord_3060226, baseEnd_3060226] using wordTrace_append hprefix tailTrace_3060226
  have hstable : (prefixWord ++ tailWord_3060226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060226).length < 2 ^ (prefixWord ++ tailWord_3060226).sum := by decide
  have hdescent : baseEnd_3060226 < baseStart_3060226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060250 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_3060250 : Nat := 118140960795 + 3060250 * 2 ^ 59
def prefixEnd_3060250 : Nat := 4983230072969 + 3 ^ 40 * 3060250 * 2
def baseEnd_3060250 : Nat := 1571379172921756991501173

theorem tailTrace_3060250 : CollatzResearch.WordTrace tailWord_3060250 prefixEnd_3060250 1571379172921756991501173 := by
  unfold tailWord_3060250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904121790811093483722551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74410991442162915956593469 27904121790811093483722551)
  ·
    refine ⟨41856182686216640225583827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904121790811093483722551 41856182686216640225583827)
    ·
      refine ⟨62784274029324960338375741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41856182686216640225583827 62784274029324960338375741)
      ·
        refine ⟨23544102760996860126890903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62784274029324960338375741 23544102760996860126890903)
        ·
          refine ⟨35316154141495290190336355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23544102760996860126890903 35316154141495290190336355)
          ·
            refine ⟨52974231212242935285504533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35316154141495290190336355 52974231212242935285504533)
            ·
              refine ⟨2483167088073887591508025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52974231212242935285504533 2483167088073887591508025)
              ·
                refine ⟨1862375316055415693631019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483167088073887591508025 1862375316055415693631019)
                ·
                  refine ⟨2793562974083123540446529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862375316055415693631019 2793562974083123540446529)
                  ·
                    refine ⟨2095172230562342655334897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2793562974083123540446529 2095172230562342655334897)
                    ·
                      refine ⟨1571379172921756991501173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095172230562342655334897 1571379172921756991501173)
                      ·
                        rfl

theorem cell23_3060250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_3060250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060250 prefixEnd_3060250 := by exact prefixLift 3060250
  have htrace : WordTrace (prefixWord ++ tailWord_3060250) baseStart_3060250 baseEnd_3060250 := by
    simpa [prefixWord, tailWord_3060250, baseEnd_3060250] using wordTrace_append hprefix tailTrace_3060250
  have hstable : (prefixWord ++ tailWord_3060250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060250).length < 2 ^ (prefixWord ++ tailWord_3060250).sum := by decide
  have hdescent : baseEnd_3060250 < baseStart_3060250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060252 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3060252 : Nat := 118140960795 + 3060252 * 2 ^ 59
def prefixEnd_3060252 : Nat := 4983230072969 + 3 ^ 40 * 3060252 * 2
def baseEnd_3060252 : Nat := 523793399961021994558721

theorem tailTrace_3060252 : CollatzResearch.WordTrace tailWord_3060252 prefixEnd_3060252 523793399961021994558721 := by
  unfold tailWord_3060252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808280054618564138231505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74411040072824752184308673 55808280054618564138231505)
  ·
    refine ⟨41856210040963923103673629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55808280054618564138231505 41856210040963923103673629)
    ·
      refine ⟨15696078765361471163877611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41856210040963923103673629 15696078765361471163877611)
      ·
        refine ⟨23544118148042206745816417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15696078765361471163877611 23544118148042206745816417)
        ·
          refine ⟨17658088611031655059362313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23544118148042206745816417 17658088611031655059362313)
          ·
            refine ⟨13243566458273741294521735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17658088611031655059362313 13243566458273741294521735)
            ·
              refine ⟨19865349687410611941782603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243566458273741294521735 19865349687410611941782603)
              ·
                refine ⟨29798024531115917912673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19865349687410611941782603 29798024531115917912673905)
                ·
                  refine ⟨22348518398336938434505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29798024531115917912673905 22348518398336938434505429)
                  ·
                    refine ⟨523793399961021994558721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22348518398336938434505429 523793399961021994558721)
                    ·
                      rfl

theorem cell23_3060252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3060252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060252 prefixEnd_3060252 := by exact prefixLift 3060252
  have htrace : WordTrace (prefixWord ++ tailWord_3060252) baseStart_3060252 baseEnd_3060252 := by
    simpa [prefixWord, tailWord_3060252, baseEnd_3060252] using wordTrace_append hprefix tailTrace_3060252
  have hstable : (prefixWord ++ tailWord_3060252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060252).length < 2 ^ (prefixWord ++ tailWord_3060252).sum := by decide
  have hdescent : baseEnd_3060252 < baseStart_3060252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060256 : List Nat := [2, 1, 1, 6, 3, 1, 1, 8]
def baseStart_3060256 : Nat := 118140960795 + 3060256 * 2 ^ 59
def prefixEnd_3060256 : Nat := 4983230072969 + 3 ^ 40 * 3060256 * 2
def baseEnd_3060256 : Nat := 58199342733543850667635

theorem tailTrace_3060256 : CollatzResearch.WordTrace tailWord_3060256 prefixEnd_3060256 58199342733543850667635 := by
  unfold tailWord_3060256
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808353000611318479804311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74411137334148424639739081 55808353000611318479804311)
  ·
    refine ⟨83712529500916977719706467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55808353000611318479804311 83712529500916977719706467)
    ·
      refine ⟨125568794251375466579559701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83712529500916977719706467 125568794251375466579559701)
      ·
        refine ⟨5886037230533224995916861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125568794251375466579559701 5886037230533224995916861)
        ·
          refine ⟨2207263961449959373468823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5886037230533224995916861 2207263961449959373468823)
          ·
            refine ⟨3310895942174939060203235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207263961449959373468823 3310895942174939060203235)
            ·
              refine ⟨4966343913262408590304853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310895942174939060203235 4966343913262408590304853)
              ·
                refine ⟨58199342733543850667635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4966343913262408590304853 58199342733543850667635)
                ·
                  rfl

theorem cell23_3060256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 8].length) (baseStart_3060256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060256 prefixEnd_3060256 := by exact prefixLift 3060256
  have htrace : WordTrace (prefixWord ++ tailWord_3060256) baseStart_3060256 baseEnd_3060256 := by
    simpa [prefixWord, tailWord_3060256, baseEnd_3060256] using wordTrace_append hprefix tailTrace_3060256
  have hstable : (prefixWord ++ tailWord_3060256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060256).length < 2 ^ (prefixWord ++ tailWord_3060256).sum := by decide
  have hdescent : baseEnd_3060256 < baseStart_3060256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060263 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3060263 : Nat := 118140960795 + 3060263 * 2 ^ 59
def prefixEnd_3060263 : Nat := 4983230072969 + 3 ^ 40 * 3060263 * 2
def baseEnd_3060263 : Nat := 1571385848170265440638613

theorem tailTrace_3060263 : CollatzResearch.WordTrace tailWord_3060263 prefixEnd_3060263 1571385848170265440638613 := by
  unfold tailWord_3060263
  simp only [CollatzResearch.WordTrace]
  refine ⟨111616961312197277155113443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74411307541464851436742295 111616961312197277155113443)
  ·
    refine ⟨167425441968295915732670165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111616961312197277155113443 167425441968295915732670165)
    ·
      refine ⟨3924033796131935524984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 167425441968295915732670165 3924033796131935524984457)
      ·
        refine ⟨2943025347098951643738343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3924033796131935524984457 2943025347098951643738343)
        ·
          refine ⟨4414538020648427465607515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943025347098951643738343 4414538020648427465607515)
          ·
            refine ⟨6621807030972641198411273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414538020648427465607515 6621807030972641198411273)
            ·
              refine ⟨4966355273229480898808455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621807030972641198411273 4966355273229480898808455)
              ·
                refine ⟨7449532909844221348212683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966355273229480898808455 7449532909844221348212683)
                ·
                  refine ⟨11174299364766332022319025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449532909844221348212683 11174299364766332022319025)
                  ·
                    refine ⟨8380724523574749016739269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11174299364766332022319025 8380724523574749016739269)
                    ·
                      refine ⟨1571385848170265440638613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8380724523574749016739269 1571385848170265440638613)
                      ·
                        rfl

theorem cell23_3060263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3060263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060263 prefixEnd_3060263 := by exact prefixLift 3060263
  have htrace : WordTrace (prefixWord ++ tailWord_3060263) baseStart_3060263 baseEnd_3060263 := by
    simpa [prefixWord, tailWord_3060263, baseEnd_3060263] using wordTrace_append hprefix tailTrace_3060263
  have hstable : (prefixWord ++ tailWord_3060263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060263).length < 2 ^ (prefixWord ++ tailWord_3060263).sum := by decide
  have hdescent : baseEnd_3060263 < baseStart_3060263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060266 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3060266 : Nat := 118140960795 + 3060266 * 2 ^ 59
def prefixEnd_3060266 : Nat := 4983230072969 + 3 ^ 40 * 3060266 * 2
def baseEnd_3060266 : Nat := 1571387388612228928901099

theorem tailTrace_3060266 : CollatzResearch.WordTrace tailWord_3060266 prefixEnd_3060266 1571387388612228928901099 := by
  unfold tailWord_3060266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904267682796602166868163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74411380487457605778315101 27904267682796602166868163)
  ·
    refine ⟨41856401524194903250302245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904267682796602166868163 41856401524194903250302245)
    ·
      refine ⟨7848075285786544359431671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41856401524194903250302245 7848075285786544359431671)
      ·
        refine ⟨11772112928679816539147507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848075285786544359431671 11772112928679816539147507)
        ·
          refine ⟨17658169393019724808721261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772112928679816539147507 17658169393019724808721261)
          ·
            refine ⟨6621813522382396803270473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17658169393019724808721261 6621813522382396803270473)
            ·
              refine ⟨4966360141786797602452855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621813522382396803270473 4966360141786797602452855)
              ·
                refine ⟨7449540212680196403679283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966360141786797602452855 7449540212680196403679283)
                ·
                  refine ⟨11174310319020294605518925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449540212680196403679283 11174310319020294605518925)
                  ·
                    refine ⟨4190366369632610477069597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11174310319020294605518925 4190366369632610477069597)
                    ·
                      refine ⟨1571387388612228928901099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190366369632610477069597 1571387388612228928901099)
                      ·
                        rfl

theorem cell23_3060266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3060266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060266 prefixEnd_3060266 := by exact prefixLift 3060266
  have htrace : WordTrace (prefixWord ++ tailWord_3060266) baseStart_3060266 baseEnd_3060266 := by
    simpa [prefixWord, tailWord_3060266, baseEnd_3060266] using wordTrace_append hprefix tailTrace_3060266
  have hstable : (prefixWord ++ tailWord_3060266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060266).length < 2 ^ (prefixWord ++ tailWord_3060266).sum := by decide
  have hdescent : baseEnd_3060266 < baseStart_3060266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060293 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_3060293 : Nat := 118140960795 + 3060293 * 2 ^ 59
def prefixEnd_3060293 : Nat := 4983230072969 + 3 ^ 40 * 3060293 * 2
def baseEnd_3060293 : Nat := 1571401252589900323263475

theorem tailTrace_3060293 : CollatzResearch.WordTrace tailWord_3060293 prefixEnd_3060293 1571401252589900323263475 := by
  unfold tailWord_3060293
  simp only [CollatzResearch.WordTrace]
  refine ⟨111618055502088592278705533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74412037001392394852470355 111618055502088592278705533)
  ·
    refine ⟨41856770813283222104514575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111618055502088592278705533 41856770813283222104514575)
    ·
      refine ⟨62785156219924833156771863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41856770813283222104514575 62785156219924833156771863)
      ·
        refine ⟨94177734329887249735157795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62785156219924833156771863 94177734329887249735157795)
        ·
          refine ⟨141266601494830874602736693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94177734329887249735157795 141266601494830874602736693)
          ·
            refine ⟨13243743890140394494006565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141266601494830874602736693 13243743890140394494006565)
            ·
              refine ⟨2483201979401323967626231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13243743890140394494006565 2483201979401323967626231)
              ·
                refine ⟨3724802969101985951439347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483201979401323967626231 3724802969101985951439347)
                ·
                  refine ⟨5587204453652978927159021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724802969101985951439347 5587204453652978927159021)
                  ·
                    refine ⟨2095201670119867097684633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5587204453652978927159021 2095201670119867097684633)
                    ·
                      refine ⟨1571401252589900323263475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095201670119867097684633 1571401252589900323263475)
                      ·
                        rfl

theorem cell23_3060293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_3060293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060293 prefixEnd_3060293 := by exact prefixLift 3060293
  have htrace : WordTrace (prefixWord ++ tailWord_3060293) baseStart_3060293 baseEnd_3060293 := by
    simpa [prefixWord, tailWord_3060293, baseEnd_3060293] using wordTrace_append hprefix tailTrace_3060293
  have hstable : (prefixWord ++ tailWord_3060293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060293).length < 2 ^ (prefixWord ++ tailWord_3060293).sum := by decide
  have hdescent : baseEnd_3060293 < baseStart_3060293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060312 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 7]
def baseStart_3060312 : Nat := 118140960795 + 3060312 * 2 ^ 59
def prefixEnd_3060312 : Nat := 4983230072969 + 3 ^ 40 * 3060312 * 2
def baseEnd_3060312 : Nat := 174601223191370638769543

theorem tailTrace_3060312 : CollatzResearch.WordTrace tailWord_3060312 prefixEnd_3060312 174601223191370638769543 := by
  unfold tailWord_3060312
  simp only [CollatzResearch.WordTrace]
  refine ⟨55809374244509879261823595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74412498992679839015764793 55809374244509879261823595)
  ·
    refine ⟨83714061366764818892735393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55809374244509879261823595 83714061366764818892735393)
    ·
      refine ⟨62785546025073614169551545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83714061366764818892735393 62785546025073614169551545)
      ·
        refine ⟨47089159518805210627163659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62785546025073614169551545 47089159518805210627163659)
        ·
          refine ⟨70633739278207815940745489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47089159518805210627163659 70633739278207815940745489)
          ·
            refine ⟨52975304458655861955559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70633739278207815940745489 52975304458655861955559117)
            ·
              refine ⟨19865739171995948233334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52975304458655861955559117 19865739171995948233334669)
              ·
                refine ⟨7449652189498480587500501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19865739171995948233334669 7449652189498480587500501)
                ·
                  refine ⟨174601223191370638769543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7449652189498480587500501 174601223191370638769543)
                  ·
                    rfl

theorem cell23_3060312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_3060312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060312 prefixEnd_3060312 := by exact prefixLift 3060312
  have htrace : WordTrace (prefixWord ++ tailWord_3060312) baseStart_3060312 baseEnd_3060312 := by
    simpa [prefixWord, tailWord_3060312, baseEnd_3060312] using wordTrace_append hprefix tailTrace_3060312
  have hstable : (prefixWord ++ tailWord_3060312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060312).length < 2 ^ (prefixWord ++ tailWord_3060312).sum := by decide
  have hdescent : baseEnd_3060312 < baseStart_3060312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060359 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3060359 : Nat := 118140960795 + 3060359 * 2 ^ 59
def prefixEnd_3060359 : Nat := 4983230072969 + 3 ^ 40 * 3060359 * 2
def baseEnd_3060359 : Nat := 523811714104365688346057

theorem tailTrace_3060359 : CollatzResearch.WordTrace tailWord_3060359 prefixEnd_3060359 523811714104365688346057 := by
  unfold tailWord_3060359
  simp only [CollatzResearch.WordTrace]
  refine ⟨111620462719849485550608131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74413641813232990367072087 111620462719849485550608131)
  ·
    refine ⟨167430694079774228325912197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111620462719849485550608131 167430694079774228325912197)
    ·
      refine ⟨31393255139957667811108537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167430694079774228325912197 31393255139957667811108537)
      ·
        refine ⟨23544941354968250858331403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31393255139957667811108537 23544941354968250858331403)
        ·
          refine ⟨35317412032452376287497105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23544941354968250858331403 35317412032452376287497105)
          ·
            refine ⟨26488059024339282215622829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35317412032452376287497105 26488059024339282215622829)
            ·
              refine ⟨9933022134127230830858561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26488059024339282215622829 9933022134127230830858561)
              ·
                refine ⟨7449766600595423123143921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9933022134127230830858561 7449766600595423123143921)
                ·
                  refine ⟨5587324950446567342357941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449766600595423123143921 5587324950446567342357941)
                  ·
                    refine ⟨523811714104365688346057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5587324950446567342357941 523811714104365688346057)
                    ·
                      rfl

theorem cell23_3060359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3060359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060359 prefixEnd_3060359 := by exact prefixLift 3060359
  have htrace : WordTrace (prefixWord ++ tailWord_3060359) baseStart_3060359 baseEnd_3060359 := by
    simpa [prefixWord, tailWord_3060359, baseEnd_3060359] using wordTrace_append hprefix tailTrace_3060359
  have hstable : (prefixWord ++ tailWord_3060359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060359).length < 2 ^ (prefixWord ++ tailWord_3060359).sum := by decide
  have hdescent : baseEnd_3060359 < baseStart_3060359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060366 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3060366 : Nat := 118140960795 + 3060366 * 2 ^ 59
def prefixEnd_3060366 : Nat := 4983230072969 + 3 ^ 40 * 3060366 * 2
def baseEnd_3060366 : Nat := 1571438736677678537650639

theorem tailTrace_3060366 : CollatzResearch.WordTrace tailWord_3060366 prefixEnd_3060366 1571438736677678537650639 := by
  unfold tailWord_3060366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952589753853015718264119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74413812020549417164075301 13952589753853015718264119)
  ·
    refine ⟨20928884630779523577396179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13952589753853015718264119 20928884630779523577396179)
    ·
      refine ⟨31393326946169285366094269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20928884630779523577396179 31393326946169285366094269)
      ·
        refine ⟨11772497604813482012285351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31393326946169285366094269 11772497604813482012285351)
        ·
          refine ⟨17658746407220223018428027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772497604813482012285351 17658746407220223018428027)
          ·
            refine ⟨26488119610830334527642041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17658746407220223018428027 26488119610830334527642041)
            ·
              refine ⟨19866089708122750895731531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26488119610830334527642041 19866089708122750895731531)
              ·
                refine ⟨29799134562184126343597297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866089708122750895731531 29799134562184126343597297)
                ·
                  refine ⟨22349350921638094757697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29799134562184126343597297 22349350921638094757697973)
                  ·
                    refine ⟨2095251648903571383534185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22349350921638094757697973 2095251648903571383534185)
                    ·
                      refine ⟨1571438736677678537650639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095251648903571383534185 1571438736677678537650639)
                      ·
                        rfl

theorem cell23_3060366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3060366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060366 prefixEnd_3060366 := by exact prefixLift 3060366
  have htrace : WordTrace (prefixWord ++ tailWord_3060366) baseStart_3060366 baseEnd_3060366 := by
    simpa [prefixWord, tailWord_3060366, baseEnd_3060366] using wordTrace_append hprefix tailTrace_3060366
  have hstable : (prefixWord ++ tailWord_3060366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060366).length < 2 ^ (prefixWord ++ tailWord_3060366).sum := by decide
  have hdescent : baseEnd_3060366 < baseStart_3060366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060379 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 6, 2]
def baseStart_3060379 : Nat := 118140960795 + 3060379 * 2 ^ 59
def prefixEnd_3060379 : Nat := 4983230072969 + 3 ^ 40 * 3060379 * 2
def baseEnd_3060379 : Nat := 1571445411926186986788079

theorem tailTrace_3060379 : CollatzResearch.WordTrace tailWord_3060379 prefixEnd_3060379 1571445411926186986788079 := by
  unfold tailWord_3060379
  simp only [CollatzResearch.WordTrace]
  refine ⟨111621192179777028966336191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74414128119851352644224127 111621192179777028966336191)
  ·
    refine ⟨167431788269665543449504287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111621192179777028966336191 167431788269665543449504287)
    ·
      refine ⟨251147682404498315174256431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167431788269665543449504287 251147682404498315174256431)
      ·
        refine ⟨376721523606747472761384647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251147682404498315174256431 376721523606747472761384647)
        ·
          refine ⟨565082285410121209142076971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376721523606747472761384647 565082285410121209142076971)
          ·
            refine ⟨847623428115181813713115457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565082285410121209142076971 847623428115181813713115457)
            ·
              refine ⟨635717571086386360284836593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847623428115181813713115457 635717571086386360284836593)
              ·
                refine ⟨476788178314789770213627445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635717571086386360284836593 476788178314789770213627445)
                ·
                  refine ⟨44698891717011540957527573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476788178314789770213627445 44698891717011540957527573)
                  ·
                    refine ⟨2095260549234915982384105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44698891717011540957527573 2095260549234915982384105)
                    ·
                      refine ⟨1571445411926186986788079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095260549234915982384105 1571445411926186986788079)
                      ·
                        rfl

theorem cell23_3060379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6, 2].length) (baseStart_3060379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060379 prefixEnd_3060379 := by exact prefixLift 3060379
  have htrace : WordTrace (prefixWord ++ tailWord_3060379) baseStart_3060379 baseEnd_3060379 := by
    simpa [prefixWord, tailWord_3060379, baseEnd_3060379] using wordTrace_append hprefix tailTrace_3060379
  have hstable : (prefixWord ++ tailWord_3060379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060379).length < 2 ^ (prefixWord ++ tailWord_3060379).sum := by decide
  have hdescent : baseEnd_3060379 < baseStart_3060379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060389 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_3060389 : Nat := 118140960795 + 3060389 * 2 ^ 59
def prefixEnd_3060389 : Nat := 4983230072969 + 3 ^ 40 * 3060389 * 2
def baseEnd_3060389 : Nat := 523816848910910649221011

theorem tailTrace_3060389 : CollatzResearch.WordTrace tailWord_3060389 prefixEnd_3060389 523816848910910649221011 := by
  unfold tailWord_3060389
  simp only [CollatzResearch.WordTrace]
  refine ⟨111621556909740800674200221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74414371273160533782800147 111621556909740800674200221)
  ·
    refine ⟨41858083841152800252825083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111621556909740800674200221 41858083841152800252825083)
    ·
      refine ⟨62787125761729200379237625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41858083841152800252825083 62787125761729200379237625)
      ·
        refine ⟨47090344321296900284428219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62787125761729200379237625 47090344321296900284428219)
        ·
          refine ⟨70635516481945350426642329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47090344321296900284428219 70635516481945350426642329)
          ·
            refine ⟨52976637361459012819981747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70635516481945350426642329 52976637361459012819981747)
            ·
              refine ⟨79464956042188519229972621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52976637361459012819981747 79464956042188519229972621)
              ·
                refine ⟨29799358515820694711239733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79464956042188519229972621 29799358515820694711239733)
                ·
                  refine ⟨2793689860858190129178725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29799358515820694711239733 2793689860858190129178725)
                  ·
                    refine ⟨523816848910910649221011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793689860858190129178725 523816848910910649221011)
                    ·
                      rfl

theorem cell23_3060389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_3060389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060389 prefixEnd_3060389 := by exact prefixLift 3060389
  have htrace : WordTrace (prefixWord ++ tailWord_3060389) baseStart_3060389 baseEnd_3060389 := by
    simpa [prefixWord, tailWord_3060389, baseEnd_3060389] using wordTrace_append hprefix tailTrace_3060389
  have hstable : (prefixWord ++ tailWord_3060389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060389).length < 2 ^ (prefixWord ++ tailWord_3060389).sum := by decide
  have hdescent : baseEnd_3060389 < baseStart_3060389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060416 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_3060416 : Nat := 118140960795 + 3060416 * 2 ^ 59
def prefixEnd_3060416 : Nat := 4983230072969 + 3 ^ 40 * 3060416 * 2
def baseEnd_3060416 : Nat := 1571464410710403342025409

theorem tailTrace_3060416 : CollatzResearch.WordTrace tailWord_3060416 prefixEnd_3060416 1571464410710403342025409 := by
  unfold tailWord_3060416
  simp only [CollatzResearch.WordTrace]
  refine ⟨55811270840321492142716551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74415027787095322856955401 55811270840321492142716551)
  ·
    refine ⟨83716906260482238214074827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55811270840321492142716551 83716906260482238214074827)
    ·
      refine ⟨125575359390723357321112241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83716906260482238214074827 125575359390723357321112241)
      ·
        refine ⟨94181519543042517990834181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125575359390723357321112241 94181519543042517990834181)
        ·
          refine ⟨17659034914320472123281409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94181519543042517990834181 17659034914320472123281409)
          ·
            refine ⟨13244276185740354092461057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17659034914320472123281409 13244276185740354092461057)
            ·
              refine ⟨9933207139305265569345793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13244276185740354092461057 9933207139305265569345793)
              ·
                refine ⟨7449905354478949177009345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9933207139305265569345793 7449905354478949177009345)
                ·
                  refine ⟨5587429015859211882757009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449905354478949177009345 5587429015859211882757009)
                  ·
                    refine ⟨4190571761894408912067757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587429015859211882757009 4190571761894408912067757)
                    ·
                      refine ⟨1571464410710403342025409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4190571761894408912067757 1571464410710403342025409)
                      ·
                        rfl

theorem cell23_3060416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_3060416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060416 prefixEnd_3060416 := by exact prefixLift 3060416
  have htrace : WordTrace (prefixWord ++ tailWord_3060416) baseStart_3060416 baseEnd_3060416 := by
    simpa [prefixWord, tailWord_3060416, baseEnd_3060416] using wordTrace_append hprefix tailTrace_3060416
  have hstable : (prefixWord ++ tailWord_3060416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060416).length < 2 ^ (prefixWord ++ tailWord_3060416).sum := by decide
  have hdescent : baseEnd_3060416 < baseStart_3060416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060489 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_3060489 : Nat := 118140960795 + 3060489 * 2 ^ 59
def prefixEnd_3060489 : Nat := 4983230072969 + 3 ^ 40 * 3060489 * 2
def baseEnd_3060489 : Nat := 1571501894798181556412573

theorem tailTrace_3060489 : CollatzResearch.WordTrace tailWord_3060489 prefixEnd_3060489 1571501894798181556412573 := by
  unfold tailWord_3060489
  simp only [CollatzResearch.WordTrace]
  refine ⟨111625204209378517752840521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74416802806252345168560347 111625204209378517752840521)
  ·
    refine ⟨83718903157033888314630391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111625204209378517752840521 83718903157033888314630391)
    ·
      refine ⟨125578354735550832471945587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83718903157033888314630391 125578354735550832471945587)
      ·
        refine ⟨188367532103326248707918381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125578354735550832471945587 188367532103326248707918381)
        ·
          refine ⟨70637824538747343265469393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188367532103326248707918381 70637824538747343265469393)
          ·
            refine ⟨52978368404060507449102045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70637824538747343265469393 52978368404060507449102045)
            ·
              refine ⟨19866888151522690293413267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52978368404060507449102045 19866888151522690293413267)
              ·
                refine ⟨29800332227284035440119901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19866888151522690293413267 29800332227284035440119901)
                ·
                  refine ⟨11175124585231513290044963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29800332227284035440119901 11175124585231513290044963)
                  ·
                    refine ⟨16762686877847269935067445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11175124585231513290044963 16762686877847269935067445)
                    ·
                      refine ⟨1571501894798181556412573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16762686877847269935067445 1571501894798181556412573)
                      ·
                        rfl

theorem cell23_3060489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_3060489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060489 prefixEnd_3060489 := by exact prefixLift 3060489
  have htrace : WordTrace (prefixWord ++ tailWord_3060489) baseStart_3060489 baseEnd_3060489 := by
    simpa [prefixWord, tailWord_3060489, baseEnd_3060489] using wordTrace_append hprefix tailTrace_3060489
  have hstable : (prefixWord ++ tailWord_3060489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060489).length < 2 ^ (prefixWord ++ tailWord_3060489).sum := by decide
  have hdescent : baseEnd_3060489 < baseStart_3060489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060499 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_3060499 : Nat := 118140960795 + 3060499 * 2 ^ 59
def prefixEnd_3060499 : Nat := 4983230072969 + 3 ^ 40 * 3060499 * 2
def baseEnd_3060499 : Nat := 1571507029604726517287527

theorem tailTrace_3060499 : CollatzResearch.WordTrace tailWord_3060499 prefixEnd_3060499 1571507029604726517287527 := by
  unfold tailWord_3060499
  simp only [CollatzResearch.WordTrace]
  refine ⟨111625568939342289460704551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74417045959561526307136367 111625568939342289460704551)
  ·
    refine ⟨167438353409013434191056827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111625568939342289460704551 167438353409013434191056827)
    ·
      refine ⟨251157530113520151286585241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167438353409013434191056827 251157530113520151286585241)
      ·
        refine ⟨188368147585140113464938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251157530113520151286585241 188368147585140113464938931)
        ·
          refine ⟨282552221377710170197408397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188368147585140113464938931 282552221377710170197408397)
          ·
            refine ⟨105957083016641313824028149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282552221377710170197408397 105957083016641313824028149)
            ·
              refine ⟨9933476532810123171002639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105957083016641313824028149 9933476532810123171002639)
              ·
                refine ⟨14900214799215184756503959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9933476532810123171002639 14900214799215184756503959)
                ·
                  refine ⟨22350322198822777134755939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14900214799215184756503959 22350322198822777134755939)
                  ·
                    refine ⟨33525483298234165702133909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22350322198822777134755939 33525483298234165702133909)
                    ·
                      refine ⟨1571507029604726517287527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33525483298234165702133909 1571507029604726517287527)
                      ·
                        rfl

theorem cell23_3060499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_3060499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060499 prefixEnd_3060499 := by exact prefixLift 3060499
  have htrace : WordTrace (prefixWord ++ tailWord_3060499) baseStart_3060499 baseEnd_3060499 := by
    simpa [prefixWord, tailWord_3060499, baseEnd_3060499] using wordTrace_append hprefix tailTrace_3060499
  have hstable : (prefixWord ++ tailWord_3060499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060499).length < 2 ^ (prefixWord ++ tailWord_3060499).sum := by decide
  have hdescent : baseEnd_3060499 < baseStart_3060499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060526 : List Nat := [4, 1, 3, 2, 1, 1, 11]
def baseStart_3060526 : Nat := 118140960795 + 3060526 * 2 ^ 59
def prefixEnd_3060526 : Nat := 4983230072969 + 3 ^ 40 * 3060526 * 2
def baseEnd_3060526 : Nat := 19401492513362937180863

theorem tailTrace_3060526 : CollatzResearch.WordTrace tailWord_3060526 prefixEnd_3060526 19401492513362937180863 := by
  unfold tailWord_3060526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13953319213780559133992179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74417702473496315381291621 13953319213780559133992179)
  ·
    refine ⟨20929978820670838700988269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13953319213780559133992179 20929978820670838700988269)
    ·
      refine ⟨7848742057751564512870601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20929978820670838700988269 7848742057751564512870601)
      ·
        refine ⟨5886556543313673384652951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7848742057751564512870601 5886556543313673384652951)
        ·
          refine ⟨8829834814970510076979427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886556543313673384652951 8829834814970510076979427)
          ·
            refine ⟨13244752222455765115469141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829834814970510076979427 13244752222455765115469141)
            ·
              refine ⟨19401492513362937180863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13244752222455765115469141 19401492513362937180863)
              ·
                rfl

theorem cell23_3060526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 11].length) (baseStart_3060526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060526 prefixEnd_3060526 := by exact prefixLift 3060526
  have htrace : WordTrace (prefixWord ++ tailWord_3060526) baseStart_3060526 baseEnd_3060526 := by
    simpa [prefixWord, tailWord_3060526, baseEnd_3060526] using wordTrace_append hprefix tailTrace_3060526
  have hstable : (prefixWord ++ tailWord_3060526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060526).length < 2 ^ (prefixWord ++ tailWord_3060526).sum := by decide
  have hdescent : baseEnd_3060526 < baseStart_3060526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060549 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_3060549 : Nat := 118140960795 + 3060549 * 2 ^ 59
def prefixEnd_3060549 : Nat := 4983230072969 + 3 ^ 40 * 3060549 * 2
def baseEnd_3060549 : Nat := 1571532703637451321662297

theorem tailTrace_3060549 : CollatzResearch.WordTrace tailWord_3060549 prefixEnd_3060549 1571532703637451321662297 := by
  unfold tailWord_3060549
  simp only [CollatzResearch.WordTrace]
  refine ⟨111627392589161148000024701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74418261726107432000016467 111627392589161148000024701)
  ·
    refine ⟨41860272220935430500009263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111627392589161148000024701 41860272220935430500009263)
    ·
      refine ⟨62790408331403145750013895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41860272220935430500009263 62790408331403145750013895)
      ·
        refine ⟨94185612497104718625020843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62790408331403145750013895 94185612497104718625020843)
        ·
          refine ⟨141278418745657077937531265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94185612497104718625020843 141278418745657077937531265)
          ·
            refine ⟨105958814059242808453148449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141278418745657077937531265 105958814059242808453148449)
            ·
              refine ⟨79469110544432106339861337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105958814059242808453148449 79469110544432106339861337)
              ·
                refine ⟨59601832908324079754896003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79469110544432106339861337 59601832908324079754896003)
                ·
                  refine ⟨89402749362486119632344005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59601832908324079754896003 89402749362486119632344005)
                  ·
                    refine ⟨16763015505466147431064501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89402749362486119632344005 16763015505466147431064501)
                    ·
                      refine ⟨1571532703637451321662297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16763015505466147431064501 1571532703637451321662297)
                      ·
                        rfl

theorem cell23_3060549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_3060549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060549 prefixEnd_3060549 := by exact prefixLift 3060549
  have htrace : WordTrace (prefixWord ++ tailWord_3060549) baseStart_3060549 baseEnd_3060549 := by
    simpa [prefixWord, tailWord_3060549, baseEnd_3060549] using wordTrace_append hprefix tailTrace_3060549
  have hstable : (prefixWord ++ tailWord_3060549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060549).length < 2 ^ (prefixWord ++ tailWord_3060549).sum := by decide
  have hdescent : baseEnd_3060549 < baseStart_3060549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060599 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 11]
def baseStart_3060599 : Nat := 118140960795 + 3060599 * 2 ^ 59
def prefixEnd_3060599 : Nat := 4983230072969 + 3 ^ 40 * 3060599 * 2
def baseEnd_3060599 : Nat := 174617597518908458448563

theorem tailTrace_3060599 : CollatzResearch.WordTrace tailWord_3060599 prefixEnd_3060599 174617597518908458448563 := by
  unfold tailWord_3060599
  simp only [CollatzResearch.WordTrace]
  refine ⟨111629216238980006539344851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74419477492653337692896567 111629216238980006539344851)
  ·
    refine ⟨167443824358470009809017277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111629216238980006539344851 167443824358470009809017277)
    ·
      refine ⟨62791434134426253678381479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167443824358470009809017277 62791434134426253678381479)
      ·
        refine ⟨94187151201639380517572219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62791434134426253678381479 94187151201639380517572219)
        ·
          refine ⟨141280726802459070776358329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94187151201639380517572219 141280726802459070776358329)
          ·
            refine ⟨105960545101844303082268747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141280726802459070776358329 105960545101844303082268747)
            ·
              refine ⟨158940817652766454623403121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105960545101844303082268747 158940817652766454623403121)
              ·
                refine ⟨119205613239574840967552341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158940817652766454623403121 119205613239574840967552341)
                ·
                  refine ⟨174617597518908458448563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 119205613239574840967552341 174617597518908458448563)
                  ·
                    rfl

theorem cell23_3060599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 11].length) (baseStart_3060599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060599 prefixEnd_3060599 := by exact prefixLift 3060599
  have htrace : WordTrace (prefixWord ++ tailWord_3060599) baseStart_3060599 baseEnd_3060599 := by
    simpa [prefixWord, tailWord_3060599, baseEnd_3060599] using wordTrace_append hprefix tailTrace_3060599
  have hstable : (prefixWord ++ tailWord_3060599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060599).length < 2 ^ (prefixWord ++ tailWord_3060599).sum := by decide
  have hdescent : baseEnd_3060599 < baseStart_3060599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060616 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 9]
def baseStart_3060616 : Nat := 118140960795 + 3060616 * 2 ^ 59
def prefixEnd_3060616 : Nat := 4983230072969 + 3 ^ 40 * 3060616 * 2
def baseEnd_3060616 : Nat := 174618567426811395502721

theorem tailTrace_3060616 : CollatzResearch.WordTrace tailWord_3060616 prefixEnd_3060616 174618567426811395502721 := by
  unfold tailWord_3060616
  simp only [CollatzResearch.WordTrace]
  refine ⟨55814918139959209221356851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74419890853278945628475801 55814918139959209221356851)
  ·
    refine ⟨83722377209938813832035277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55814918139959209221356851 83722377209938813832035277)
    ·
      refine ⟨31395891453727055187013229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83722377209938813832035277 31395891453727055187013229)
      ·
        refine ⟨11773459295147645695129961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31395891453727055187013229 11773459295147645695129961)
        ·
          refine ⟨8830094471360734271347471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11773459295147645695129961 8830094471360734271347471)
          ·
            refine ⟨13245141707041101407021207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830094471360734271347471 13245141707041101407021207)
            ·
              refine ⟨19867712560561652110531811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245141707041101407021207 19867712560561652110531811)
              ·
                refine ⟨29801568840842478165797717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19867712560561652110531811 29801568840842478165797717)
                ·
                  refine ⟨174618567426811395502721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29801568840842478165797717 174618567426811395502721)
                  ·
                    rfl

theorem cell23_3060616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_3060616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060616 prefixEnd_3060616 := by exact prefixLift 3060616
  have htrace : WordTrace (prefixWord ++ tailWord_3060616) baseStart_3060616 baseEnd_3060616 := by
    simpa [prefixWord, tailWord_3060616, baseEnd_3060616] using wordTrace_append hprefix tailTrace_3060616
  have hstable : (prefixWord ++ tailWord_3060616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060616).length < 2 ^ (prefixWord ++ tailWord_3060616).sum := by decide
  have hdescent : baseEnd_3060616 < baseStart_3060616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060666 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_3060666 : Nat := 118140960795 + 3060666 * 2 ^ 59
def prefixEnd_3060666 : Nat := 4983230072969 + 3 ^ 40 * 3060666 * 2
def baseEnd_3060666 : Nat := 1571592780874027363899259

theorem tailTrace_3060666 : CollatzResearch.WordTrace tailWord_3060666 prefixEnd_3060666 1571592780874027363899259 := by
  unfold tailWord_3060666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27907914982434319245508463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74421106619824851321355901 27907914982434319245508463)
  ·
    refine ⟨41861872473651478868262695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27907914982434319245508463 41861872473651478868262695)
    ·
      refine ⟨62792808710477218302394043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41861872473651478868262695 62792808710477218302394043)
      ·
        refine ⟨94189213065715827453591065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62792808710477218302394043 94189213065715827453591065)
        ·
          refine ⟨70641909799286870590193299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94189213065715827453591065 70641909799286870590193299)
          ·
            refine ⟨105962864698930305885289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70641909799286870590193299 105962864698930305885289949)
            ·
              refine ⟨39736074262098864706983731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105962864698930305885289949 39736074262098864706983731)
              ·
                refine ⟨59604111393148297060475597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39736074262098864706983731 59604111393148297060475597)
                ·
                  refine ⟨22351541772430611397678349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59604111393148297060475597 22351541772430611397678349)
                  ·
                    refine ⟨8381828164661479274129381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22351541772430611397678349 8381828164661479274129381)
                    ·
                      refine ⟨1571592780874027363899259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8381828164661479274129381 1571592780874027363899259)
                      ·
                        rfl

theorem cell23_3060666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_3060666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060666 prefixEnd_3060666 := by exact prefixLift 3060666
  have htrace : WordTrace (prefixWord ++ tailWord_3060666) baseStart_3060666 baseEnd_3060666 := by
    simpa [prefixWord, tailWord_3060666, baseEnd_3060666] using wordTrace_append hprefix tailTrace_3060666
  have hstable : (prefixWord ++ tailWord_3060666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060666).length < 2 ^ (prefixWord ++ tailWord_3060666).sum := by decide
  have hdescent : baseEnd_3060666 < baseStart_3060666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060753 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_3060753 : Nat := 118140960795 + 3060753 * 2 ^ 59
def prefixEnd_3060753 : Nat := 4983230072969 + 3 ^ 40 * 3060753 * 2
def baseEnd_3060753 : Nat := 523879151230322841170453

theorem tailTrace_3060753 : CollatzResearch.WordTrace tailWord_3060753 prefixEnd_3060753 523879151230322841170453 := by
  unfold tailWord_3060753
  simp only [CollatzResearch.WordTrace]
  refine ⟨111634833080422090840450913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74423222053614727226967275 111634833080422090840450913)
  ·
    refine ⟨83726124810316568130338185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111634833080422090840450913 83726124810316568130338185)
    ·
      refine ⟨62794593607737426097753639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83726124810316568130338185 62794593607737426097753639)
      ·
        refine ⟨94191890411606139146630459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62794593607737426097753639 94191890411606139146630459)
        ·
          refine ⟨141287835617409208719945689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94191890411606139146630459 141287835617409208719945689)
          ·
            refine ⟨105965876713056906539959267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141287835617409208719945689 105965876713056906539959267)
            ·
              refine ⟨158948815069585359809938901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105965876713056906539959267 158948815069585359809938901)
              ·
                refine ⟨3725362853193406870545443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158948815069585359809938901 3725362853193406870545443)
                ·
                  refine ⟨5588044279790110305818165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725362853193406870545443 5588044279790110305818165)
                  ·
                    refine ⟨523879151230322841170453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5588044279790110305818165 523879151230322841170453)
                    ·
                      rfl

theorem cell23_3060753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_3060753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060753 prefixEnd_3060753 := by exact prefixLift 3060753
  have htrace : WordTrace (prefixWord ++ tailWord_3060753) baseStart_3060753 baseEnd_3060753 := by
    simpa [prefixWord, tailWord_3060753, baseEnd_3060753] using wordTrace_append hprefix tailTrace_3060753
  have hstable : (prefixWord ++ tailWord_3060753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060753).length < 2 ^ (prefixWord ++ tailWord_3060753).sum := by decide
  have hdescent : baseEnd_3060753 < baseStart_3060753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060773 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_3060773 : Nat := 118140960795 + 3060773 * 2 ^ 59
def prefixEnd_3060773 : Nat := 4983230072969 + 3 ^ 40 * 3060773 * 2
def baseEnd_3060773 : Nat := 1571647723304058445261267

theorem tailTrace_3060773 : CollatzResearch.WordTrace tailWord_3060773 prefixEnd_3060773 1571647723304058445261267 := by
  unfold tailWord_3060773
  simp only [CollatzResearch.WordTrace]
  refine ⟨111635562540349634256178973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74423708360233089504119315 111635562540349634256178973)
  ·
    refine ⟨41863335952631112846067115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111635562540349634256178973 41863335952631112846067115)
    ·
      refine ⟨62795003928946669269100673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41863335952631112846067115 62795003928946669269100673)
      ·
        refine ⟨47096252946710001951825505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62795003928946669269100673 47096252946710001951825505)
        ·
          refine ⟨35322189710032501463869129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47096252946710001951825505 35322189710032501463869129)
          ·
            refine ⟨26491642282524376097901847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35322189710032501463869129 26491642282524376097901847)
            ·
              refine ⟨39737463423786564146852771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26491642282524376097901847 39737463423786564146852771)
              ·
                refine ⟨59606195135679846220279157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39737463423786564146852771 59606195135679846220279157)
                ·
                  refine ⟨5588080793969985583151171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59606195135679846220279157 5588080793969985583151171)
                  ·
                    refine ⟨8382121190954978374726757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588080793969985583151171 8382121190954978374726757)
                    ·
                      refine ⟨1571647723304058445261267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8382121190954978374726757 1571647723304058445261267)
                      ·
                        rfl

theorem cell23_3060773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_3060773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060773 prefixEnd_3060773 := by exact prefixLift 3060773
  have htrace : WordTrace (prefixWord ++ tailWord_3060773) baseStart_3060773 baseEnd_3060773 := by
    simpa [prefixWord, tailWord_3060773, baseEnd_3060773] using wordTrace_append hprefix tailTrace_3060773
  have hstable : (prefixWord ++ tailWord_3060773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060773).length < 2 ^ (prefixWord ++ tailWord_3060773).sum := by decide
  have hdescent : baseEnd_3060773 < baseStart_3060773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060801 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3060801 : Nat := 118140960795 + 3060801 * 2 ^ 59
def prefixEnd_3060801 : Nat := 4983230072969 + 3 ^ 40 * 3060801 * 2
def baseEnd_3060801 : Nat := 1571662100762384335711139

theorem tailTrace_3060801 : CollatzResearch.WordTrace tailWord_3060801 prefixEnd_3060801 1571662100762384335711139 := by
  unfold tailWord_3060801
  simp only [CollatzResearch.WordTrace]
  refine ⟨111636583784248195038198257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74424389189498796692132171 111636583784248195038198257)
  ·
    refine ⟨83727437838186146278648693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111636583784248195038198257 83727437838186146278648693)
    ·
      refine ⟨7849447297329951213623315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83727437838186146278648693 7849447297329951213623315)
      ·
        refine ⟨11774170945994926820434973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849447297329951213623315 11774170945994926820434973)
        ·
          refine ⟨4415314104748097557663115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11774170945994926820434973 4415314104748097557663115)
          ·
            refine ⟨6622971157122146336494673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415314104748097557663115 6622971157122146336494673)
            ·
              refine ⟨4967228367841609752371005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6622971157122146336494673 4967228367841609752371005)
              ·
                refine ⟨1862710637940603657139127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4967228367841609752371005 1862710637940603657139127)
                ·
                  refine ⟨2794065956910905485708691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862710637940603657139127 2794065956910905485708691)
                  ·
                    refine ⟨4191098935366358228563037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2794065956910905485708691 4191098935366358228563037)
                    ·
                      refine ⟨1571662100762384335711139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4191098935366358228563037 1571662100762384335711139)
                      ·
                        rfl

theorem cell23_3060801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3060801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060801 prefixEnd_3060801 := by exact prefixLift 3060801
  have htrace : WordTrace (prefixWord ++ tailWord_3060801) baseStart_3060801 baseEnd_3060801 := by
    simpa [prefixWord, tailWord_3060801, baseEnd_3060801] using wordTrace_append hprefix tailTrace_3060801
  have hstable : (prefixWord ++ tailWord_3060801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060801).length < 2 ^ (prefixWord ++ tailWord_3060801).sum := by decide
  have hdescent : baseEnd_3060801 < baseStart_3060801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060803 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3060803 : Nat := 118140960795 + 3060803 * 2 ^ 59
def prefixEnd_3060803 : Nat := 4983230072969 + 3 ^ 40 * 3060803 * 2
def baseEnd_3060803 : Nat := 1571663127723693327886129

theorem tailTrace_3060803 : CollatzResearch.WordTrace tailWord_3060803 prefixEnd_3060803 1571663127723693327886129 := by
  unfold tailWord_3060803
  simp only [CollatzResearch.WordTrace]
  refine ⟨111636656730240949379771063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74424437820160632919847375 111636656730240949379771063)
  ·
    refine ⟨167454985095361424069656595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111636656730240949379771063 167454985095361424069656595)
    ·
      refine ⟨251182477643042136104484893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167454985095361424069656595 251182477643042136104484893)
      ·
        refine ⟨94193429116140801039181835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251182477643042136104484893 94193429116140801039181835)
        ·
          refine ⟨141290143674211201558772753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94193429116140801039181835 141290143674211201558772753)
          ·
            refine ⟨105967607755658401169079565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141290143674211201558772753 105967607755658401169079565)
            ·
              refine ⟨39737852908371900438404837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105967607755658401169079565 39737852908371900438404837)
              ·
                refine ⟨7450847420319731332200907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39737852908371900438404837 7450847420319731332200907)
                ·
                  refine ⟨11176271130479596998301361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450847420319731332200907 11176271130479596998301361)
                  ·
                    refine ⟨8382203347859697748726021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11176271130479596998301361 8382203347859697748726021)
                    ·
                      refine ⟨1571663127723693327886129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8382203347859697748726021 1571663127723693327886129)
                      ·
                        rfl

theorem cell23_3060803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3060803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060803 prefixEnd_3060803 := by exact prefixLift 3060803
  have htrace : WordTrace (prefixWord ++ tailWord_3060803) baseStart_3060803 baseEnd_3060803 := by
    simpa [prefixWord, tailWord_3060803, baseEnd_3060803] using wordTrace_append hprefix tailTrace_3060803
  have hstable : (prefixWord ++ tailWord_3060803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060803).length < 2 ^ (prefixWord ++ tailWord_3060803).sum := by decide
  have hdescent : baseEnd_3060803 < baseStart_3060803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060807 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_3060807 : Nat := 118140960795 + 3060807 * 2 ^ 59
def prefixEnd_3060807 : Nat := 4983230072969 + 3 ^ 40 * 3060807 * 2
def baseEnd_3060807 : Nat := 1571665181646311312236111

theorem tailTrace_3060807 : CollatzResearch.WordTrace tailWord_3060807 prefixEnd_3060807 1571665181646311312236111 := by
  unfold tailWord_3060807
  simp only [CollatzResearch.WordTrace]
  refine ⟨111636802622226458062916675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74424535081484305375277783 111636802622226458062916675)
  ·
    refine ⟨167455203933339687094375013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111636802622226458062916675 167455203933339687094375013)
    ·
      refine ⟨31397850737501191330195315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167455203933339687094375013 31397850737501191330195315)
      ·
        refine ⟨47096776106251786995292973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31397850737501191330195315 47096776106251786995292973)
        ·
          refine ⟨17661291039844420123234865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47096776106251786995292973 17661291039844420123234865)
          ·
            refine ⟨13245968279883315092426149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17661291039844420123234865 13245968279883315092426149)
            ·
              refine ⟨2483619052478121579829903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13245968279883315092426149 2483619052478121579829903)
              ·
                refine ⟨3725428578717182369744855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483619052478121579829903 3725428578717182369744855)
                ·
                  refine ⟨5588142868075773554617283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725428578717182369744855 5588142868075773554617283)
                  ·
                    refine ⟨8382214302113660331925925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588142868075773554617283 8382214302113660331925925)
                    ·
                      refine ⟨1571665181646311312236111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8382214302113660331925925 1571665181646311312236111)
                      ·
                        rfl

theorem cell23_3060807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_3060807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060807 prefixEnd_3060807 := by exact prefixLift 3060807
  have htrace : WordTrace (prefixWord ++ tailWord_3060807) baseStart_3060807 baseEnd_3060807 := by
    simpa [prefixWord, tailWord_3060807, baseEnd_3060807] using wordTrace_append hprefix tailTrace_3060807
  have hstable : (prefixWord ++ tailWord_3060807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060807).length < 2 ^ (prefixWord ++ tailWord_3060807).sum := by decide
  have hdescent : baseEnd_3060807 < baseStart_3060807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060824 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_3060824 : Nat := 118140960795 + 3060824 * 2 ^ 59
def prefixEnd_3060824 : Nat := 4983230072969 + 3 ^ 40 * 3060824 * 2
def baseEnd_3060824 : Nat := 1571673910817437745723533

theorem tailTrace_3060824 : CollatzResearch.WordTrace tailWord_3060824 prefixEnd_3060824 1571673910817437745723533 := by
  unfold tailWord_3060824
  simp only [CollatzResearch.WordTrace]
  refine ⟨55818711331582434983142763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74424948442109913310857017 55818711331582434983142763)
  ·
    refine ⟨83728066997373652474714145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55818711331582434983142763 83728066997373652474714145)
    ·
      refine ⟨62796050248030239356035609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83728066997373652474714145 62796050248030239356035609)
      ·
        refine ⟨47097037686022679517026707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62796050248030239356035609 47097037686022679517026707)
        ·
          refine ⟨70645556529034019275540061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47097037686022679517026707 70645556529034019275540061)
          ·
            refine ⟨26492083698387757228327523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70645556529034019275540061 26492083698387757228327523)
            ·
              refine ⟨39738125547581635842491285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26492083698387757228327523 39738125547581635842491285)
              ·
                refine ⟨1862724635042889180116779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39738125547581635842491285 1862724635042889180116779)
                ·
                  refine ⟨2794086952564333770175169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862724635042889180116779 2794086952564333770175169)
                  ·
                    refine ⟨2095565214423250327631377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2794086952564333770175169 2095565214423250327631377)
                    ·
                      refine ⟨1571673910817437745723533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095565214423250327631377 1571673910817437745723533)
                      ·
                        rfl

theorem cell23_3060824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_3060824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060824 prefixEnd_3060824 := by exact prefixLift 3060824
  have htrace : WordTrace (prefixWord ++ tailWord_3060824) baseStart_3060824 baseEnd_3060824 := by
    simpa [prefixWord, tailWord_3060824, baseEnd_3060824] using wordTrace_append hprefix tailTrace_3060824
  have hstable : (prefixWord ++ tailWord_3060824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060824).length < 2 ^ (prefixWord ++ tailWord_3060824).sum := by decide
  have hdescent : baseEnd_3060824 < baseStart_3060824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060867 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 1, 3, 2]
def baseStart_3060867 : Nat := 118140960795 + 3060867 * 2 ^ 59
def prefixEnd_3060867 : Nat := 4983230072969 + 3 ^ 40 * 3060867 * 2
def baseEnd_3060867 : Nat := 1571695990485581077485835

theorem tailTrace_3060867 : CollatzResearch.WordTrace tailWord_3060867 prefixEnd_3060867 1571695990485581077485835 := by
  unfold tailWord_3060867
  simp only [CollatzResearch.WordTrace]
  refine ⟨111638991002009088310100855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74425994001339392206733903 111638991002009088310100855)
  ·
    refine ⟨167458486503013632465151283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111638991002009088310100855 167458486503013632465151283)
    ·
      refine ⟨251187729754520448697726925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167458486503013632465151283 251187729754520448697726925)
      ·
        refine ⟨94195398657945168261647597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251187729754520448697726925 94195398657945168261647597)
        ·
          refine ⟨35323274496729438098117849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94195398657945168261647597 35323274496729438098117849)
          ·
            refine ⟨26492455872547078573588387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35323274496729438098117849 26492455872547078573588387)
            ·
              refine ⟨39738683808820617860382581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26492455872547078573588387 39738683808820617860382581)
              ·
                refine ⟨3725501607076932924410867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39738683808820617860382581 3725501607076932924410867)
                ·
                  refine ⟨5588252410615399386616301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725501607076932924410867 5588252410615399386616301)
                  ·
                    refine ⟨2095594653980774769981113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5588252410615399386616301 2095594653980774769981113)
                    ·
                      refine ⟨1571695990485581077485835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095594653980774769981113 1571695990485581077485835)
                      ·
                        rfl

theorem cell23_3060867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_3060867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060867 prefixEnd_3060867 := by exact prefixLift 3060867
  have htrace : WordTrace (prefixWord ++ tailWord_3060867) baseStart_3060867 baseEnd_3060867 := by
    simpa [prefixWord, tailWord_3060867, baseEnd_3060867] using wordTrace_append hprefix tailTrace_3060867
  have hstable : (prefixWord ++ tailWord_3060867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060867).length < 2 ^ (prefixWord ++ tailWord_3060867).sum := by decide
  have hdescent : baseEnd_3060867 < baseStart_3060867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2]
def baseStart_3060880 : Nat := 118140960795 + 3060880 * 2 ^ 59
def prefixEnd_3060880 : Nat := 4983230072969 + 3 ^ 40 * 3060880 * 2
def baseEnd_3060880 : Nat := 1571702665734089526623275

theorem tailTrace_3060880 : CollatzResearch.WordTrace tailWord_3060880 prefixEnd_3060880 1571702665734089526623275 := by
  unfold tailWord_3060880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55819732575480995765162047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74426310100641327686882729 55819732575480995765162047)
  ·
    refine ⟨83729598863221493647743071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55819732575480995765162047 83729598863221493647743071)
    ·
      refine ⟨125594398294832240471614607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83729598863221493647743071 125594398294832240471614607)
      ·
        refine ⟨188391597442248360707421911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125594398294832240471614607 188391597442248360707421911)
        ·
          refine ⟨282587396163372541061132867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188391597442248360707421911 282587396163372541061132867)
          ·
            refine ⟨423881094245058811591699301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282587396163372541061132867 423881094245058811591699301)
            ·
              refine ⟨79477705170948527173443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423881094245058811591699301 79477705170948527173443619)
              ·
                refine ⟨119216557756422790760165429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79477705170948527173443619 119216557756422790760165429)
                ·
                  refine ⟨11176552289664636633765509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119216557756422790760165429 11176552289664636633765509)
                  ·
                    refine ⟨2095603554312119368831033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11176552289664636633765509 2095603554312119368831033)
                    ·
                      refine ⟨1571702665734089526623275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095603554312119368831033 1571702665734089526623275)
                      ·
                        rfl

theorem cell23_3060880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2].length) (baseStart_3060880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060880 prefixEnd_3060880 := by exact prefixLift 3060880
  have htrace : WordTrace (prefixWord ++ tailWord_3060880) baseStart_3060880 baseEnd_3060880 := by
    simpa [prefixWord, tailWord_3060880, baseEnd_3060880] using wordTrace_append hprefix tailTrace_3060880
  have hstable : (prefixWord ++ tailWord_3060880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060880).length < 2 ^ (prefixWord ++ tailWord_3060880).sum := by decide
  have hdescent : baseEnd_3060880 < baseStart_3060880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060897 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3060897 : Nat := 118140960795 + 3060897 * 2 ^ 59
def prefixEnd_3060897 : Nat := 4983230072969 + 3 ^ 40 * 3060897 * 2
def baseEnd_3060897 : Nat := 1571711394905215960110697

theorem tailTrace_3060897 : CollatzResearch.WordTrace tailWord_3060897 prefixEnd_3060897 1571711394905215960110697 := by
  unfold tailWord_3060897
  simp only [CollatzResearch.WordTrace]
  refine ⟨111640085191900403433692945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74426723461266935622461963 111640085191900403433692945)
  ·
    refine ⟨83730063893925302575269709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111640085191900403433692945 83730063893925302575269709)
    ·
      refine ⟨31398773960221988465726141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83730063893925302575269709 31398773960221988465726141)
      ·
        refine ⟨11774540235083245674647303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31398773960221988465726141 11774540235083245674647303)
        ·
          refine ⟨17661810352624868511970955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774540235083245674647303 17661810352624868511970955)
          ·
            refine ⟨26492715528937302767956433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17661810352624868511970955 26492715528937302767956433)
            ·
              refine ⟨19869536646702977075967325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26492715528937302767956433 19869536646702977075967325)
              ·
                refine ⟨7451076242513616403487747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19869536646702977075967325 7451076242513616403487747)
                ·
                  refine ⟨11176614363770424605231621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451076242513616403487747 11176614363770424605231621)
                  ·
                    refine ⟨2095615193206954613480929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11176614363770424605231621 2095615193206954613480929)
                    ·
                      refine ⟨1571711394905215960110697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095615193206954613480929 1571711394905215960110697)
                      ·
                        rfl

theorem cell23_3060897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3060897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060897 prefixEnd_3060897 := by exact prefixLift 3060897
  have htrace : WordTrace (prefixWord ++ tailWord_3060897) baseStart_3060897 baseEnd_3060897 := by
    simpa [prefixWord, tailWord_3060897, baseEnd_3060897] using wordTrace_append hprefix tailTrace_3060897
  have hstable : (prefixWord ++ tailWord_3060897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060897).length < 2 ^ (prefixWord ++ tailWord_3060897).sum := by decide
  have hdescent : baseEnd_3060897 < baseStart_3060897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060900 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3060900 : Nat := 118140960795 + 3060900 * 2 ^ 59
def prefixEnd_3060900 : Nat := 4983230072969 + 3 ^ 40 * 3060900 * 2
def baseEnd_3060900 : Nat := 1571712935347179448373183

theorem tailTrace_3060900 : CollatzResearch.WordTrace tailWord_3060900 prefixEnd_3060900 1571712935347179448373183 := by
  unfold tailWord_3060900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55820097305444767473026077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74426796407259689964034769 55820097305444767473026077)
  ·
    refine ⟨20932536489541787802384779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55820097305444767473026077 20932536489541787802384779)
    ·
      refine ⟨31398804734312681703577169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20932536489541787802384779 31398804734312681703577169)
      ·
        refine ⟨23549103550734511277682877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31398804734312681703577169 23549103550734511277682877)
        ·
          refine ⟨8830913831525441729131079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23549103550734511277682877 8830913831525441729131079)
          ·
            refine ⟨13246370747288162593696619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830913831525441729131079 13246370747288162593696619)
            ·
              refine ⟨19869556120932243890544929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246370747288162593696619 19869556120932243890544929)
              ·
                refine ⟨14902167090699182917908697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19869556120932243890544929 14902167090699182917908697)
                ·
                  refine ⟨11176625318024387188431523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14902167090699182917908697 11176625318024387188431523)
                  ·
                    refine ⟨16764937977036580782647285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11176625318024387188431523 16764937977036580782647285)
                    ·
                      refine ⟨1571712935347179448373183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16764937977036580782647285 1571712935347179448373183)
                      ·
                        rfl

theorem cell23_3060900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3060900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060900 prefixEnd_3060900 := by exact prefixLift 3060900
  have htrace : WordTrace (prefixWord ++ tailWord_3060900) baseStart_3060900 baseEnd_3060900 := by
    simpa [prefixWord, tailWord_3060900, baseEnd_3060900] using wordTrace_append hprefix tailTrace_3060900
  have hstable : (prefixWord ++ tailWord_3060900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060900).length < 2 ^ (prefixWord ++ tailWord_3060900).sum := by decide
  have hdescent : baseEnd_3060900 < baseStart_3060900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060933 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_3060933 : Nat := 118140960795 + 3060933 * 2 ^ 59
def prefixEnd_3060933 : Nat := 4983230072969 + 3 ^ 40 * 3060933 * 2
def baseEnd_3060933 : Nat := 523909960069592606420177

theorem tailTrace_3060933 : CollatzResearch.WordTrace tailWord_3060933 prefixEnd_3060933 523909960069592606420177 := by
  unfold tailWord_3060933
  simp only [CollatzResearch.WordTrace]
  refine ⟨111641398219769981582003453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74427598813179987721335635 111641398219769981582003453)
  ·
    refine ⟨41865524332413743093251295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111641398219769981582003453 41865524332413743093251295)
    ·
      refine ⟨62798286498620614639876943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41865524332413743093251295 62798286498620614639876943)
      ·
        refine ⟨94197429747930921959815415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62798286498620614639876943 94197429747930921959815415)
        ·
          refine ⟨141296144621896382939723123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94197429747930921959815415 141296144621896382939723123)
          ·
            refine ⟨211944216932844574409584685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141296144621896382939723123 211944216932844574409584685)
            ·
              refine ⟨79479081349816715403594257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211944216932844574409584685 79479081349816715403594257)
              ·
                refine ⟨59609311012362536552695693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79479081349816715403594257 59609311012362536552695693)
                ·
                  refine ⟨22353491629635951207260885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59609311012362536552695693 22353491629635951207260885)
                  ·
                    refine ⟨523909960069592606420177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22353491629635951207260885 523909960069592606420177)
                    ·
                      rfl

theorem cell23_3060933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_3060933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060933 prefixEnd_3060933 := by exact prefixLift 3060933
  have htrace : WordTrace (prefixWord ++ tailWord_3060933) baseStart_3060933 baseEnd_3060933 := by
    simpa [prefixWord, tailWord_3060933, baseEnd_3060933] using wordTrace_append hprefix tailTrace_3060933
  have hstable : (prefixWord ++ tailWord_3060933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060933).length < 2 ^ (prefixWord ++ tailWord_3060933).sum := by decide
  have hdescent : baseEnd_3060933 < baseStart_3060933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060943 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_3060943 : Nat := 118140960795 + 3060943 * 2 ^ 59
def prefixEnd_3060943 : Nat := 4983230072969 + 3 ^ 40 * 3060943 * 2
def baseEnd_3060943 : Nat := 1571735015015322780135485

theorem tailTrace_3060943 : CollatzResearch.WordTrace tailWord_3060943 prefixEnd_3060943 1571735015015322780135485 := by
  unfold tailWord_3060943
  simp only [CollatzResearch.WordTrace]
  refine ⟨111641762949733753289867483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74427841966489168859911655 111641762949733753289867483)
  ·
    refine ⟨167462644424600629934801225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111641762949733753289867483 167462644424600629934801225)
    ·
      refine ⟨125596983318450472451100919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167462644424600629934801225 125596983318450472451100919)
      ·
        refine ⟨188395474977675708676651379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125596983318450472451100919 188395474977675708676651379)
        ·
          refine ⟨282593212466513563014977069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188395474977675708676651379 282593212466513563014977069)
          ·
            refine ⟨105972454674942586130616401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282593212466513563014977069 105972454674942586130616401)
            ·
              refine ⟨79479341006206939597962301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105972454674942586130616401 79479341006206939597962301)
              ·
                refine ⟨29804752877327602349235863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79479341006206939597962301 29804752877327602349235863)
                ·
                  refine ⟨44707129315991403523853795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29804752877327602349235863 44707129315991403523853795)
                  ·
                    refine ⟨67060693973987105285780693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44707129315991403523853795 67060693973987105285780693)
                    ·
                      refine ⟨1571735015015322780135485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67060693973987105285780693 1571735015015322780135485)
                      ·
                        rfl

theorem cell23_3060943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_3060943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060943 prefixEnd_3060943 := by exact prefixLift 3060943
  have htrace : WordTrace (prefixWord ++ tailWord_3060943) baseStart_3060943 baseEnd_3060943 := by
    simpa [prefixWord, tailWord_3060943, baseEnd_3060943] using wordTrace_append hprefix tailTrace_3060943
  have hstable : (prefixWord ++ tailWord_3060943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060943).length < 2 ^ (prefixWord ++ tailWord_3060943).sum := by decide
  have hdescent : baseEnd_3060943 < baseStart_3060943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060967 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3060967 : Nat := 118140960795 + 3060967 * 2 ^ 59
def prefixEnd_3060967 : Nat := 4983230072969 + 3 ^ 40 * 3060967 * 2
def baseEnd_3060967 : Nat := 523915779517010228745125

theorem tailTrace_3060967 : CollatzResearch.WordTrace tailWord_3060967 prefixEnd_3060967 523915779517010228745125 := by
  unfold tailWord_3060967
  simp only [CollatzResearch.WordTrace]
  refine ⟨111642638301646805388741155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74428425534431203592494103 111642638301646805388741155)
  ·
    refine ⟨167463957452470208083111733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111642638301646805388741155 167463957452470208083111733)
    ·
      refine ⟨15699746011169082007791725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167463957452470208083111733 15699746011169082007791725)
      ·
        refine ⟨5887404754188405752921897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15699746011169082007791725 5887404754188405752921897)
        ·
          refine ⟨4415553565641304314691423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5887404754188405752921897 4415553565641304314691423)
          ·
            refine ⟨6623330348461956472037135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415553565641304314691423 6623330348461956472037135)
            ·
              refine ⟨9934995522692934708055703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623330348461956472037135 9934995522692934708055703)
              ·
                refine ⟨14902493284039402062083555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9934995522692934708055703 14902493284039402062083555)
                ·
                  refine ⟨22353739926059103093125333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14902493284039402062083555 22353739926059103093125333)
                  ·
                    refine ⟨523915779517010228745125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22353739926059103093125333 523915779517010228745125)
                    ·
                      rfl

theorem cell23_3060967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3060967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060967 prefixEnd_3060967 := by exact prefixLift 3060967
  have htrace : WordTrace (prefixWord ++ tailWord_3060967) baseStart_3060967 baseEnd_3060967 := by
    simpa [prefixWord, tailWord_3060967, baseEnd_3060967] using wordTrace_append hprefix tailTrace_3060967
  have hstable : (prefixWord ++ tailWord_3060967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060967).length < 2 ^ (prefixWord ++ tailWord_3060967).sum := by decide
  have hdescent : baseEnd_3060967 < baseStart_3060967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3060997 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_3060997 : Nat := 118140960795 + 3060997 * 2 ^ 59
def prefixEnd_3060997 : Nat := 4983230072969 + 3 ^ 40 * 3060997 * 2
def baseEnd_3060997 : Nat := 523920914323555189620079

theorem tailTrace_3060997 : CollatzResearch.WordTrace tailWord_3060997 prefixEnd_3060997 523920914323555189620079 := by
  unfold tailWord_3060997
  simp only [CollatzResearch.WordTrace]
  refine ⟨111643732491538120512333245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74429154994358747008222163 111643732491538120512333245)
  ·
    refine ⟨41866399684326795192124967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111643732491538120512333245 41866399684326795192124967)
    ·
      refine ⟨62799599526490192788187451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41866399684326795192124967 62799599526490192788187451)
      ·
        refine ⟨94199399289735289182281177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62799599526490192788187451 94199399289735289182281177)
        ·
          refine ⟨70649549467301466886710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94199399289735289182281177 70649549467301466886710883)
          ·
            refine ⟨105974324200952200330066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70649549467301466886710883 105974324200952200330066325)
            ·
              refine ⟨4967546446919634390471859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105974324200952200330066325 4967546446919634390471859)
              ·
                refine ⟨7451319670379451585707789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967546446919634390471859 7451319670379451585707789)
                ·
                  refine ⟨2794244876392294344640421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7451319670379451585707789 2794244876392294344640421)
                  ·
                    refine ⟨523920914323555189620079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794244876392294344640421 523920914323555189620079)
                    ·
                      rfl

theorem cell23_3060997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_3060997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3060997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3060997 prefixEnd_3060997 := by exact prefixLift 3060997
  have htrace : WordTrace (prefixWord ++ tailWord_3060997) baseStart_3060997 baseEnd_3060997 := by
    simpa [prefixWord, tailWord_3060997, baseEnd_3060997] using wordTrace_append hprefix tailTrace_3060997
  have hstable : (prefixWord ++ tailWord_3060997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3060997).length < 2 ^ (prefixWord ++ tailWord_3060997).sum := by decide
  have hdescent : baseEnd_3060997 < baseStart_3060997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3060997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061100 : List Nat := [2, 2, 1, 1, 5, 12]
def baseStart_3061100 : Nat := 118140960795 + 3061100 * 2 ^ 59
def prefixEnd_3061100 : Nat := 4983230072969 + 3 ^ 40 * 3061100 * 2
def baseEnd_3061100 : Nat := 6468377084271928666141

theorem tailTrace_3061100 : CollatzResearch.WordTrace tailWord_3061100 prefixEnd_3061100 6468377084271928666141 := by
  unfold tailWord_3061100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55823744605082484551666377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74431659473443312735555169 55823744605082484551666377)
  ·
    refine ⟨41867808453811863413749783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55823744605082484551666377 41867808453811863413749783)
    ·
      refine ⟨62801712680717795120624675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41867808453811863413749783 62801712680717795120624675)
      ·
        refine ⟨94202569021076692680937013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62801712680717795120624675 94202569021076692680937013)
        ·
          refine ⟨8831490845725939938837845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94202569021076692680937013 8831490845725939938837845)
          ·
            refine ⟨6468377084271928666141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8831490845725939938837845 6468377084271928666141)
            ·
              rfl

theorem cell23_3061100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 12].length) (baseStart_3061100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061100 prefixEnd_3061100 := by exact prefixLift 3061100
  have htrace : WordTrace (prefixWord ++ tailWord_3061100) baseStart_3061100 baseEnd_3061100 := by
    simpa [prefixWord, tailWord_3061100, baseEnd_3061100] using wordTrace_append hprefix tailTrace_3061100
  have hstable : (prefixWord ++ tailWord_3061100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061100).length < 2 ^ (prefixWord ++ tailWord_3061100).sum := by decide
  have hdescent : baseEnd_3061100 < baseStart_3061100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061104 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_3061104 : Nat := 118140960795 + 3061104 * 2 ^ 59
def prefixEnd_3061104 : Nat := 4983230072969 + 3 ^ 40 * 3061104 * 2
def baseEnd_3061104 : Nat := 523939228466898883407415

theorem tailTrace_3061104 : CollatzResearch.WordTrace tailWord_3061104 prefixEnd_3061104 523939228466898883407415 := by
  unfold tailWord_3061104
  simp only [CollatzResearch.WordTrace]
  refine ⟨55823817551075238893239183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74431756734766985190985577 55823817551075238893239183)
  ·
    refine ⟨83735726326612858339858775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55823817551075238893239183 83735726326612858339858775)
    ·
      refine ⟨125603589489919287509788163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83735726326612858339858775 125603589489919287509788163)
      ·
        refine ⟨188405384234878931264682245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125603589489919287509788163 188405384234878931264682245)
        ·
          refine ⟨35326009544039799612127921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188405384234878931264682245 35326009544039799612127921)
          ·
            refine ⟨26494507158029849709095941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35326009544039799612127921 26494507158029849709095941)
            ·
              refine ⟨4967720092130596820455489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26494507158029849709095941 4967720092130596820455489)
              ·
                refine ⟨3725790069097947615341617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4967720092130596820455489 3725790069097947615341617)
                ·
                  refine ⟨2794342551823460711506213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3725790069097947615341617 2794342551823460711506213)
                  ·
                    refine ⟨523939228466898883407415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794342551823460711506213 523939228466898883407415)
                    ·
                      rfl

theorem cell23_3061104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_3061104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061104 prefixEnd_3061104 := by exact prefixLift 3061104
  have htrace : WordTrace (prefixWord ++ tailWord_3061104) baseStart_3061104 baseEnd_3061104 := by
    simpa [prefixWord, tailWord_3061104, baseEnd_3061104] using wordTrace_append hprefix tailTrace_3061104
  have hstable : (prefixWord ++ tailWord_3061104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061104).length < 2 ^ (prefixWord ++ tailWord_3061104).sum := by decide
  have hdescent : baseEnd_3061104 < baseStart_3061104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061120 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3061120 : Nat := 118140960795 + 3061120 * 2 ^ 59
def prefixEnd_3061120 : Nat := 4983230072969 + 3 ^ 40 * 3061120 * 2
def baseEnd_3061120 : Nat := 1571825901091168587622171

theorem tailTrace_3061120 : CollatzResearch.WordTrace tailWord_3061120 prefixEnd_3061120 1571825901091168587622171 := by
  unfold tailWord_3061120
  simp only [CollatzResearch.WordTrace]
  refine ⟨55824109335046256259530407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74432145780061675012707209 55824109335046256259530407)
  ·
    refine ⟨83736164002569384389295611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55824109335046256259530407 83736164002569384389295611)
    ·
      refine ⟨125604246003854076583943417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83736164002569384389295611 125604246003854076583943417)
      ·
        refine ⟨94203184502890557437957563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125604246003854076583943417 94203184502890557437957563)
        ·
          refine ⟨141304776754335836156936345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94203184502890557437957563 141304776754335836156936345)
          ·
            refine ⟨105978582565751877117702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141304776754335836156936345 105978582565751877117702259)
            ·
              refine ⟨158967873848627815676553389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105978582565751877117702259 158967873848627815676553389)
              ·
                refine ⟨59612952693235430878707521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158967873848627815676553389 59612952693235430878707521)
                ·
                  refine ⟨44709714519926573159030641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59612952693235430878707521 44709714519926573159030641)
                  ·
                    refine ⟨33532285889944929869272981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44709714519926573159030641 33532285889944929869272981)
                    ·
                      refine ⟨1571825901091168587622171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33532285889944929869272981 1571825901091168587622171)
                      ·
                        rfl

theorem cell23_3061120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3061120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061120 prefixEnd_3061120 := by exact prefixLift 3061120
  have htrace : WordTrace (prefixWord ++ tailWord_3061120) baseStart_3061120 baseEnd_3061120 := by
    simpa [prefixWord, tailWord_3061120, baseEnd_3061120] using wordTrace_append hprefix tailTrace_3061120
  have hstable : (prefixWord ++ tailWord_3061120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061120).length < 2 ^ (prefixWord ++ tailWord_3061120).sum := by decide
  have hdescent : baseEnd_3061120 < baseStart_3061120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061124 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3061124 : Nat := 118140960795 + 3061124 * 2 ^ 59
def prefixEnd_3061124 : Nat := 4983230072969 + 3 ^ 40 * 3061124 * 2
def baseEnd_3061124 : Nat := 1571827955013786571972153

theorem tailTrace_3061124 : CollatzResearch.WordTrace tailWord_3061124 prefixEnd_3061124 1571827955013786571972153 := by
  unfold tailWord_3061124
  simp only [CollatzResearch.WordTrace]
  refine ⟨55824182281039010601103213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74432243041385347468137617 55824182281039010601103213)
  ·
    refine ⟨20934068355389628975413705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55824182281039010601103213 20934068355389628975413705)
    ·
      refine ⟨15700551266542221731560279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20934068355389628975413705 15700551266542221731560279)
      ·
        refine ⟨23550826899813332597340419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15700551266542221731560279 23550826899813332597340419)
        ·
          refine ⟨35326240349719998896010629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23550826899813332597340419 35326240349719998896010629)
          ·
            refine ⟨6623670065572499793001993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35326240349719998896010629 6623670065572499793001993)
            ·
              refine ⟨4967752549179374844751495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623670065572499793001993 4967752549179374844751495)
              ·
                refine ⟨7451628823769062267127243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967752549179374844751495 7451628823769062267127243)
                ·
                  refine ⟨11177443235653593400690865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451628823769062267127243 11177443235653593400690865)
                  ·
                    refine ⟨8383082426740195050518149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11177443235653593400690865 8383082426740195050518149)
                    ·
                      refine ⟨1571827955013786571972153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8383082426740195050518149 1571827955013786571972153)
                      ·
                        rfl

theorem cell23_3061124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3061124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061124 prefixEnd_3061124 := by exact prefixLift 3061124
  have htrace : WordTrace (prefixWord ++ tailWord_3061124) baseStart_3061124 baseEnd_3061124 := by
    simpa [prefixWord, tailWord_3061124, baseEnd_3061124] using wordTrace_append hprefix tailTrace_3061124
  have hstable : (prefixWord ++ tailWord_3061124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061124).length < 2 ^ (prefixWord ++ tailWord_3061124).sum := by decide
  have hdescent : baseEnd_3061124 < baseStart_3061124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061148 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3061148 : Nat := 118140960795 + 3061148 * 2 ^ 59
def prefixEnd_3061148 : Nat := 4983230072969 + 3 ^ 40 * 3061148 * 2
def baseEnd_3061148 : Nat := 1571840278549494478072043

theorem tailTrace_3061148 : CollatzResearch.WordTrace tailWord_3061148 prefixEnd_3061148 1571840278549494478072043 := by
  unfold tailWord_3061148
  simp only [CollatzResearch.WordTrace]
  refine ⟨55824619956995536650540049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74432826609327382200720065 55824619956995536650540049)
  ·
    refine ⟨41868464967746652487905037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55824619956995536650540049 41868464967746652487905037)
    ·
      refine ⟨15700674362904994682964389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41868464967746652487905037 15700674362904994682964389)
      ·
        refine ⟨2943876443044686503055823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15700674362904994682964389 2943876443044686503055823)
        ·
          refine ⟨4415814664567029754583735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943876443044686503055823 4415814664567029754583735)
          ·
            refine ⟨6623721996850544631875603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415814664567029754583735 6623721996850544631875603)
            ·
              refine ⟨9935582995275816947813405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623721996850544631875603 9935582995275816947813405)
              ·
                refine ⟨3725843623228431355430027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9935582995275816947813405 3725843623228431355430027)
                ·
                  refine ⟨5588765434842647033145041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725843623228431355430027 5588765434842647033145041)
                  ·
                    refine ⟨4191574076131985274858781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5588765434842647033145041 4191574076131985274858781)
                    ·
                      refine ⟨1571840278549494478072043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4191574076131985274858781 1571840278549494478072043)
                      ·
                        rfl

theorem cell23_3061148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3061148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061148 prefixEnd_3061148 := by exact prefixLift 3061148
  have htrace : WordTrace (prefixWord ++ tailWord_3061148) baseStart_3061148 baseEnd_3061148 := by
    simpa [prefixWord, tailWord_3061148, baseEnd_3061148] using wordTrace_append hprefix tailTrace_3061148
  have hstable : (prefixWord ++ tailWord_3061148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061148).length < 2 ^ (prefixWord ++ tailWord_3061148).sum := by decide
  have hdescent : baseEnd_3061148 < baseStart_3061148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061187 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3]
def baseStart_3061187 : Nat := 118140960795 + 3061187 * 2 ^ 59
def prefixEnd_3061187 : Nat := 4983230072969 + 3 ^ 40 * 3061187 * 2
def baseEnd_3061187 : Nat := 1571860304295019825484363

theorem tailTrace_3061187 : CollatzResearch.WordTrace tailWord_3061187 prefixEnd_3061187 1571860304295019825484363 := by
  unfold tailWord_3061187
  simp only [CollatzResearch.WordTrace]
  refine ⟨111650662360849782961749815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74433774907233188641166543 111650662360849782961749815)
  ·
    refine ⟨167475993541274674442624723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111650662360849782961749815 167475993541274674442624723)
    ·
      refine ⟨251213990311912011663937085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167475993541274674442624723 251213990311912011663937085)
      ·
        refine ⟨94205246366967004373976407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251213990311912011663937085 94205246366967004373976407)
        ·
          refine ⟨141307869550450506560964611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94205246366967004373976407 141307869550450506560964611)
          ·
            refine ⟨211961804325675759841446917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141307869550450506560964611 211961804325675759841446917)
            ·
              refine ⟨39742838311064204970271297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211961804325675759841446917 39742838311064204970271297)
              ·
                refine ⟨29807128733298153727703473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39742838311064204970271297 29807128733298153727703473)
                ·
                  refine ⟨22355346549973615295777605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29807128733298153727703473 22355346549973615295777605)
                  ·
                    refine ⟨4191627478120052867958301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22355346549973615295777605 4191627478120052867958301)
                    ·
                      refine ⟨1571860304295019825484363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4191627478120052867958301 1571860304295019825484363)
                      ·
                        rfl

theorem cell23_3061187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_3061187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061187 prefixEnd_3061187 := by exact prefixLift 3061187
  have htrace : WordTrace (prefixWord ++ tailWord_3061187) baseStart_3061187 baseEnd_3061187 := by
    simpa [prefixWord, tailWord_3061187, baseEnd_3061187] using wordTrace_append hprefix tailTrace_3061187
  have hstable : (prefixWord ++ tailWord_3061187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061187).length < 2 ^ (prefixWord ++ tailWord_3061187).sum := by decide
  have hdescent : baseEnd_3061187 < baseStart_3061187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061188 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3061188 : Nat := 118140960795 + 3061188 * 2 ^ 59
def prefixEnd_3061188 : Nat := 4983230072969 + 3 ^ 40 * 3061188 * 2
def baseEnd_3061188 : Nat := 1571860817775674321571859

theorem tailTrace_3061188 : CollatzResearch.WordTrace tailWord_3061188 prefixEnd_3061188 1571860817775674321571859 := by
  unfold tailWord_3061188
  simp only [CollatzResearch.WordTrace]
  refine ⟨55825349416923080066268109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74433799222564106755024145 55825349416923080066268109)
  ·
    refine ⟨20934506031346155024850541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55825349416923080066268109 20934506031346155024850541)
    ·
      refine ⟨7850439761754808134318953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20934506031346155024850541 7850439761754808134318953)
      ·
        refine ⟨5887829821316106100739215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7850439761754808134318953 5887829821316106100739215)
        ·
          refine ⟨8831744731974159151108823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887829821316106100739215 8831744731974159151108823)
          ·
            refine ⟨13247617097961238726663235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8831744731974159151108823 13247617097961238726663235)
            ·
              refine ⟨19871425646941858089994853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13247617097961238726663235 19871425646941858089994853)
              ·
                refine ⟨3725892308801598391874035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19871425646941858089994853 3725892308801598391874035)
                ·
                  refine ⟨5588838463202397587811053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725892308801598391874035 5588838463202397587811053)
                  ·
                    refine ⟨2095814423700899095429145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5588838463202397587811053 2095814423700899095429145)
                    ·
                      refine ⟨1571860817775674321571859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095814423700899095429145 1571860817775674321571859)
                      ·
                        rfl

theorem cell23_3061188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3061188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061188 prefixEnd_3061188 := by exact prefixLift 3061188
  have htrace : WordTrace (prefixWord ++ tailWord_3061188) baseStart_3061188 baseEnd_3061188 := by
    simpa [prefixWord, tailWord_3061188, baseEnd_3061188] using wordTrace_append hprefix tailTrace_3061188
  have hstable : (prefixWord ++ tailWord_3061188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061188).length < 2 ^ (prefixWord ++ tailWord_3061188).sum := by decide
  have hdescent : baseEnd_3061188 < baseStart_3061188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061297 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 10]
def baseStart_3061297 : Nat := 118140960795 + 3061297 * 2 ^ 59
def prefixEnd_3061297 : Nat := 4983230072969 + 3 ^ 40 * 3061297 * 2
def baseEnd_3061297 : Nat := 174657420796334932789873

theorem tailTrace_3061297 : CollatzResearch.WordTrace tailWord_3061297 prefixEnd_3061297 174657420796334932789873 := by
  unfold tailWord_3061297
  simp only [CollatzResearch.WordTrace]
  refine ⟨111654674390451271748254145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74436449593634181165502763 111654674390451271748254145)
  ·
    refine ⟨83741005792838453811190609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111654674390451271748254145 83741005792838453811190609)
    ·
      refine ⟨62805754344628840358392957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83741005792838453811190609 62805754344628840358392957)
      ·
        refine ⟨23552157879235815134397359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62805754344628840358392957 23552157879235815134397359)
        ·
          refine ⟨35328236818853722701596039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23552157879235815134397359 35328236818853722701596039)
          ·
            refine ⟨52992355228280584052394059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35328236818853722701596039 52992355228280584052394059)
            ·
              refine ⟨79488532842420876078591089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52992355228280584052394059 79488532842420876078591089)
              ·
                refine ⟨59616399631815657058943317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79488532842420876078591089 59616399631815657058943317)
                ·
                  refine ⟨174657420796334932789873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59616399631815657058943317 174657420796334932789873)
                  ·
                    rfl

theorem cell23_3061297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_3061297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061297 prefixEnd_3061297 := by exact prefixLift 3061297
  have htrace : WordTrace (prefixWord ++ tailWord_3061297) baseStart_3061297 baseEnd_3061297 := by
    simpa [prefixWord, tailWord_3061297, baseEnd_3061297] using wordTrace_append hprefix tailTrace_3061297
  have hstable : (prefixWord ++ tailWord_3061297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061297).length < 2 ^ (prefixWord ++ tailWord_3061297).sum := by decide
  have hdescent : baseEnd_3061297 < baseStart_3061297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061301 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3061301 : Nat := 118140960795 + 3061301 * 2 ^ 59
def prefixEnd_3061301 : Nat := 4983230072969 + 3 ^ 40 * 3061301 * 2
def baseEnd_3061301 : Nat := 523972947029877459819613

theorem tailTrace_3061301 : CollatzResearch.WordTrace tailWord_3061301 prefixEnd_3061301 523972947029877459819613 := by
  unfold tailWord_3061301
  simp only [CollatzResearch.WordTrace]
  refine ⟨111654820282436780431399757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74436546854957853620933171 111654820282436780431399757)
  ·
    refine ⟨41870557605913792661774909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111654820282436780431399757 41870557605913792661774909)
    ·
      refine ⟨15701459102217672248165591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41870557605913792661774909 15701459102217672248165591)
      ·
        refine ⟨23552188653326508372248387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701459102217672248165591 23552188653326508372248387)
        ·
          refine ⟨35328282979989762558372581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23552188653326508372248387 35328282979989762558372581)
          ·
            refine ⟨6624053058748080479694859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35328282979989762558372581 6624053058748080479694859)
            ·
              refine ⟨9936079588122120719542289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624053058748080479694859 9936079588122120719542289)
              ·
                refine ⟨7452059691091590539656717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9936079588122120719542289 7452059691091590539656717)
                ·
                  refine ⟨2794522384159346452371269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7452059691091590539656717 2794522384159346452371269)
                  ·
                    refine ⟨523972947029877459819613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794522384159346452371269 523972947029877459819613)
                    ·
                      rfl

theorem cell23_3061301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3061301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061301 prefixEnd_3061301 := by exact prefixLift 3061301
  have htrace : WordTrace (prefixWord ++ tailWord_3061301) baseStart_3061301 baseEnd_3061301 := by
    simpa [prefixWord, tailWord_3061301, baseEnd_3061301] using wordTrace_append hprefix tailTrace_3061301
  have hstable : (prefixWord ++ tailWord_3061301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061301).length < 2 ^ (prefixWord ++ tailWord_3061301).sum := by decide
  have hdescent : baseEnd_3061301 < baseStart_3061301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061308 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_3061308 : Nat := 118140960795 + 3061308 * 2 ^ 59
def prefixEnd_3061308 : Nat := 4983230072969 + 3 ^ 40 * 3061308 * 2
def baseEnd_3061308 : Nat := 1571922435454213852071307

theorem tailTrace_3061308 : CollatzResearch.WordTrace tailWord_3061308 prefixEnd_3061308 1571922435454213852071307 := by
  unfold tailWord_3061308
  simp only [CollatzResearch.WordTrace]
  refine ⟨55827537796705710313452289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74436717062274280417936385 55827537796705710313452289)
  ·
    refine ⟨41870653347529282735089217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55827537796705710313452289 41870653347529282735089217)
    ·
      refine ⟨31402990010646962051316913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41870653347529282735089217 31402990010646962051316913)
      ·
        refine ⟨23552242507985221538487685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31402990010646962051316913 23552242507985221538487685)
        ·
          refine ⟨4416045470247229038466441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23552242507985221538487685 4416045470247229038466441)
          ·
            refine ⟨3312034102685421778849831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416045470247229038466441 3312034102685421778849831)
            ·
              refine ⟨4968051154028132668274747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312034102685421778849831 4968051154028132668274747)
              ·
                refine ⟨7452076731042199002412121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968051154028132668274747 7452076731042199002412121)
                ·
                  refine ⟨5589057548281649251809091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452076731042199002412121 5589057548281649251809091)
                  ·
                    refine ⟨8383586322422473877713637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589057548281649251809091 8383586322422473877713637)
                    ·
                      refine ⟨1571922435454213852071307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8383586322422473877713637 1571922435454213852071307)
                      ·
                        rfl

theorem cell23_3061308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_3061308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061308 prefixEnd_3061308 := by exact prefixLift 3061308
  have htrace : WordTrace (prefixWord ++ tailWord_3061308) baseStart_3061308 baseEnd_3061308 := by
    simpa [prefixWord, tailWord_3061308, baseEnd_3061308] using wordTrace_append hprefix tailTrace_3061308
  have hstable : (prefixWord ++ tailWord_3061308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061308).length < 2 ^ (prefixWord ++ tailWord_3061308).sum := by decide
  have hdescent : baseEnd_3061308 < baseStart_3061308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061311 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_3061311 : Nat := 118140960795 + 3061311 * 2 ^ 59
def prefixEnd_3061311 : Nat := 4983230072969 + 3 ^ 40 * 3061311 * 2
def baseEnd_3061311 : Nat := 1571923975896177340333793

theorem tailTrace_3061311 : CollatzResearch.WordTrace tailWord_3061311 prefixEnd_3061311 1571923975896177340333793 := by
  unfold tailWord_3061311
  simp only [CollatzResearch.WordTrace]
  refine ⟨111655185012400552139263787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74436790008267034759509191 111655185012400552139263787)
  ·
    refine ⟨167482777518600828208895681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111655185012400552139263787 167482777518600828208895681)
    ·
      refine ⟨125612083138950621156671761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167482777518600828208895681 125612083138950621156671761)
      ·
        refine ⟨94209062354212965867503821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125612083138950621156671761 94209062354212965867503821)
        ·
          refine ⟨35328398382829862200313933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94209062354212965867503821 35328398382829862200313933)
          ·
            refine ⟨13248149393561198325117725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35328398382829862200313933 13248149393561198325117725)
            ·
              refine ⟨4968056022585449371919147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13248149393561198325117725 4968056022585449371919147)
              ·
                refine ⟨7452084033878174057878721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968056022585449371919147 7452084033878174057878721)
                ·
                  refine ⟨5589063025408630543409041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452084033878174057878721 5589063025408630543409041)
                  ·
                    refine ⟨4191797269056472907556781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589063025408630543409041 4191797269056472907556781)
                    ·
                      refine ⟨1571923975896177340333793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4191797269056472907556781 1571923975896177340333793)
                      ·
                        rfl

theorem cell23_3061311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_3061311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061311 prefixEnd_3061311 := by exact prefixLift 3061311
  have htrace : WordTrace (prefixWord ++ tailWord_3061311) baseStart_3061311 baseEnd_3061311 := by
    simpa [prefixWord, tailWord_3061311, baseEnd_3061311] using wordTrace_append hprefix tailTrace_3061311
  have hstable : (prefixWord ++ tailWord_3061311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061311).length < 2 ^ (prefixWord ++ tailWord_3061311).sum := by decide
  have hdescent : baseEnd_3061311 < baseStart_3061311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061351 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_3061351 : Nat := 118140960795 + 3061351 * 2 ^ 59
def prefixEnd_3061351 : Nat := 4983230072969 + 3 ^ 40 * 3061351 * 2
def baseEnd_3061351 : Nat := 1571944515122357183833609

theorem tailTrace_3061351 : CollatzResearch.WordTrace tailWord_3061351 prefixEnd_3061351 1571944515122357183833609 := by
  unfold tailWord_3061351
  simp only [CollatzResearch.WordTrace]
  refine ⟨111656643932255638970719907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74437762621503759313813271 111656643932255638970719907)
  ·
    refine ⟨167484965898383458456079861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111656643932255638970719907 167484965898383458456079861)
    ·
      refine ⟨15701715552973449230257487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167484965898383458456079861 15701715552973449230257487)
      ·
        refine ⟨23552573329460173845386231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701715552973449230257487 23552573329460173845386231)
        ·
          refine ⟨35328859994190260768079347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23552573329460173845386231 35328859994190260768079347)
          ·
            refine ⟨52993289991285391152119021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35328859994190260768079347 52993289991285391152119021)
            ·
              refine ⟨19872483746732021682044633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52993289991285391152119021 19872483746732021682044633)
              ·
                refine ⟨14904362810049016261533475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19872483746732021682044633 14904362810049016261533475)
                ·
                  refine ⟨22356544215073524392300213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14904362810049016261533475 22356544215073524392300213)
                  ·
                    refine ⟨2095926020163142911778145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22356544215073524392300213 2095926020163142911778145)
                    ·
                      refine ⟨1571944515122357183833609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2095926020163142911778145 1571944515122357183833609)
                      ·
                        rfl

theorem cell23_3061351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_3061351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061351 prefixEnd_3061351 := by exact prefixLift 3061351
  have htrace : WordTrace (prefixWord ++ tailWord_3061351) baseStart_3061351 baseEnd_3061351 := by
    simpa [prefixWord, tailWord_3061351, baseEnd_3061351] using wordTrace_append hprefix tailTrace_3061351
  have hstable : (prefixWord ++ tailWord_3061351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061351).length < 2 ^ (prefixWord ++ tailWord_3061351).sum := by decide
  have hdescent : baseEnd_3061351 < baseStart_3061351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061381 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_3061381 : Nat := 118140960795 + 3061381 * 2 ^ 59
def prefixEnd_3061381 : Nat := 4983230072969 + 3 ^ 40 * 3061381 * 2
def baseEnd_3061381 : Nat := 1571959919541992066458471

theorem tailTrace_3061381 : CollatzResearch.WordTrace tailWord_3061381 prefixEnd_3061381 1571959919541992066458471 := by
  unfold tailWord_3061381
  simp only [CollatzResearch.WordTrace]
  refine ⟨111657738122146954094311997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74438492081431302729541331 111657738122146954094311997)
  ·
    refine ⟨41871651795805107785366999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111657738122146954094311997 41871651795805107785366999)
    ·
      refine ⟨62807477693707661678050499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41871651795805107785366999 62807477693707661678050499)
      ·
        refine ⟨94211216540561492517075749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62807477693707661678050499 94211216540561492517075749)
        ·
          refine ⟨17664603101355279846951703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94211216540561492517075749 17664603101355279846951703)
          ·
            refine ⟨26496904652032919770427555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17664603101355279846951703 26496904652032919770427555)
            ·
              refine ⟨39745356978049379655641333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26496904652032919770427555 39745356978049379655641333)
              ·
                refine ⟨3726127216692129342716375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39745356978049379655641333 3726127216692129342716375)
                ·
                  refine ⟨5589190825038194014074563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726127216692129342716375 5589190825038194014074563)
                  ·
                    refine ⟨8383786237557291021111845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589190825038194014074563 8383786237557291021111845)
                    ·
                      refine ⟨1571959919541992066458471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8383786237557291021111845 1571959919541992066458471)
                      ·
                        rfl

theorem cell23_3061381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_3061381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061381 prefixEnd_3061381 := by exact prefixLift 3061381
  have htrace : WordTrace (prefixWord ++ tailWord_3061381) baseStart_3061381 baseEnd_3061381 := by
    simpa [prefixWord, tailWord_3061381, baseEnd_3061381] using wordTrace_append hprefix tailTrace_3061381
  have hstable : (prefixWord ++ tailWord_3061381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061381).length < 2 ^ (prefixWord ++ tailWord_3061381).sum := by decide
  have hdescent : baseEnd_3061381 < baseStart_3061381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061408 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_3061408 : Nat := 118140960795 + 3061408 * 2 ^ 59
def prefixEnd_3061408 : Nat := 4983230072969 + 3 ^ 40 * 3061408 * 2
def baseEnd_3061408 : Nat := 523991261173221153606949

theorem tailTrace_3061408 : CollatzResearch.WordTrace tailWord_3061408 prefixEnd_3061408 523991261173221153606949 := by
  unfold tailWord_3061408
  simp only [CollatzResearch.WordTrace]
  refine ⟨55829361446524568852772439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74439148595366091803696585 55829361446524568852772439)
  ·
    refine ⟨83744042169786853279158659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55829361446524568852772439 83744042169786853279158659)
    ·
      refine ⟨125616063254680279918737989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83744042169786853279158659 125616063254680279918737989)
      ·
        refine ⟨23553011860252552484763373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125616063254680279918737989 23553011860252552484763373)
        ·
          refine ⟨8832379447594707181786265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23553011860252552484763373 8832379447594707181786265)
          ·
            refine ⟨6624284585696030386339699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8832379447594707181786265 6624284585696030386339699)
            ·
              refine ⟨9936426878544045579509549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624284585696030386339699 9936426878544045579509549)
              ·
                refine ⟨3726160079454017092316081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9936426878544045579509549 3726160079454017092316081)
                ·
                  refine ⟨2794620059590512819237061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3726160079454017092316081 2794620059590512819237061)
                  ·
                    refine ⟨523991261173221153606949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794620059590512819237061 523991261173221153606949)
                    ·
                      rfl

theorem cell23_3061408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_3061408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061408 prefixEnd_3061408 := by exact prefixLift 3061408
  have htrace : WordTrace (prefixWord ++ tailWord_3061408) baseStart_3061408 baseEnd_3061408 := by
    simpa [prefixWord, tailWord_3061408, baseEnd_3061408] using wordTrace_append hprefix tailTrace_3061408
  have hstable : (prefixWord ++ tailWord_3061408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061408).length < 2 ^ (prefixWord ++ tailWord_3061408).sum := by decide
  have hdescent : baseEnd_3061408 < baseStart_3061408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061431 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_3061431 : Nat := 118140960795 + 3061431 * 2 ^ 59
def prefixEnd_3061431 : Nat := 4983230072969 + 3 ^ 40 * 3061431 * 2
def baseEnd_3061431 : Nat := 1571985593574716870833241

theorem tailTrace_3061431 : CollatzResearch.WordTrace tailWord_3061431 prefixEnd_3061431 1571985593574716870833241 := by
  unfold tailWord_3061431
  simp only [CollatzResearch.WordTrace]
  refine ⟨111659561771965812633632147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74439707847977208422421431 111659561771965812633632147)
  ·
    refine ⟨167489342657948718950448221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111659561771965812633632147 167489342657948718950448221)
    ·
      refine ⟨62808503496730769606418083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167489342657948718950448221 62808503496730769606418083)
      ·
        refine ⟨94212755245096154409627125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62808503496730769606418083 94212755245096154409627125)
        ·
          refine ⟨8832445804227764475902543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94212755245096154409627125 8832445804227764475902543)
          ·
            refine ⟨13248668706341646713853815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832445804227764475902543 13248668706341646713853815)
            ·
              refine ⟨19873003059512470070780723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13248668706341646713853815 19873003059512470070780723)
              ·
                refine ⟨29809504589268705106171085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19873003059512470070780723 29809504589268705106171085)
                ·
                  refine ⟨11178564220975764414814157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29809504589268705106171085 11178564220975764414814157)
                  ·
                    refine ⟨4191961582865911655555309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11178564220975764414814157 4191961582865911655555309)
                    ·
                      refine ⟨1571985593574716870833241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4191961582865911655555309 1571985593574716870833241)
                      ·
                        rfl

theorem cell23_3061431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_3061431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061431 prefixEnd_3061431 := by exact prefixLift 3061431
  have htrace : WordTrace (prefixWord ++ tailWord_3061431) baseStart_3061431 baseEnd_3061431 := by
    simpa [prefixWord, tailWord_3061431, baseEnd_3061431] using wordTrace_append hprefix tailTrace_3061431
  have hstable : (prefixWord ++ tailWord_3061431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061431).length < 2 ^ (prefixWord ++ tailWord_3061431).sum := by decide
  have hdescent : baseEnd_3061431 < baseStart_3061431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061462 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3061462 : Nat := 118140960795 + 3061462 * 2 ^ 59
def prefixEnd_3061462 : Nat := 4983230072969 + 3 ^ 40 * 3061462 * 2
def baseEnd_3061462 : Nat := 1572001511475006249545599

theorem tailTrace_3061462 : CollatzResearch.WordTrace tailWord_3061462 prefixEnd_3061462 1572001511475006249545599 := by
  unfold tailWord_3061462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978793277178344058000665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74440461623235669952007093 6978793277178344058000665)
  ·
    refine ⟨5234094957883758043500499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978793277178344058000665 5234094957883758043500499)
    ·
      refine ⟨7851142436825637065250749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234094957883758043500499 7851142436825637065250749)
      ·
        refine ⟨2944178413809613899469031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7851142436825637065250749 2944178413809613899469031)
        ·
          refine ⟨4416267620714420849203547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944178413809613899469031 4416267620714420849203547)
          ·
            refine ⟨6624401431071631273805321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416267620714420849203547 6624401431071631273805321)
            ·
              refine ⟨4968301073303723455353991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6624401431071631273805321 4968301073303723455353991)
              ·
                refine ⟨7452451609955585183030987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968301073303723455353991 7452451609955585183030987)
                ·
                  refine ⟨11178677414933377774546481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452451609955585183030987 11178677414933377774546481)
                  ·
                    refine ⟨8384008061200033330909861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11178677414933377774546481 8384008061200033330909861)
                    ·
                      refine ⟨1572001511475006249545599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8384008061200033330909861 1572001511475006249545599)
                      ·
                        rfl

theorem cell23_3061462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3061462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061462 prefixEnd_3061462 := by exact prefixLift 3061462
  have htrace : WordTrace (prefixWord ++ tailWord_3061462) baseStart_3061462 baseEnd_3061462 := by
    simpa [prefixWord, tailWord_3061462, baseEnd_3061462] using wordTrace_append hprefix tailTrace_3061462
  have hstable : (prefixWord ++ tailWord_3061462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061462).length < 2 ^ (prefixWord ++ tailWord_3061462).sum := by decide
  have hdescent : baseEnd_3061462 < baseStart_3061462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3061504 : Nat := 118140960795 + 3061504 * 2 ^ 59
def prefixEnd_3061504 : Nat := 4983230072969 + 3 ^ 40 * 3061504 * 2
def baseEnd_3061504 : Nat := 1572023077662495085220405

theorem tailTrace_3061504 : CollatzResearch.WordTrace tailWord_3061504 prefixEnd_3061504 1572023077662495085220405 := by
  unfold tailWord_3061504
  simp only [CollatzResearch.WordTrace]
  refine ⟨55831112150350673050519783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74441482867134230734026377 55831112150350673050519783)
  ·
    refine ⟨83746668225526009575779675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55831112150350673050519783 83746668225526009575779675)
    ·
      refine ⟨125620002338289014363669513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83746668225526009575779675 125620002338289014363669513)
      ·
        refine ⟨94215001753716760772752135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125620002338289014363669513 94215001753716760772752135)
        ·
          refine ⟨141322502630575141159128203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94215001753716760772752135 141322502630575141159128203)
          ·
            refine ⟨211983753945862711738692305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141322502630575141159128203 211983753945862711738692305)
            ·
              refine ⟨158987815459397033804019229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211983753945862711738692305 158987815459397033804019229)
              ·
                refine ⟨59620430797273887676507211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158987815459397033804019229 59620430797273887676507211)
                ·
                  refine ⟨89430646195910831514760817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59620430797273887676507211 89430646195910831514760817)
                  ·
                    refine ⟨67072984646933123636070613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89430646195910831514760817 67072984646933123636070613)
                    ·
                      refine ⟨1572023077662495085220405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67072984646933123636070613 1572023077662495085220405)
                      ·
                        rfl

theorem cell23_3061504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3061504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061504 prefixEnd_3061504 := by exact prefixLift 3061504
  have htrace : WordTrace (prefixWord ++ tailWord_3061504) baseStart_3061504 baseEnd_3061504 := by
    simpa [prefixWord, tailWord_3061504, baseEnd_3061504] using wordTrace_append hprefix tailTrace_3061504
  have hstable : (prefixWord ++ tailWord_3061504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061504).length < 2 ^ (prefixWord ++ tailWord_3061504).sum := by decide
  have hdescent : baseEnd_3061504 < baseStart_3061504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061522 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3061522 : Nat := 118140960795 + 3061522 * 2 ^ 59
def prefixEnd_3061522 : Nat := 4983230072969 + 3 ^ 40 * 3061522 * 2
def baseEnd_3061522 : Nat := 1572032320314276014795323

theorem tailTrace_3061522 : CollatzResearch.WordTrace tailWord_3061522 prefixEnd_3061522 1572032320314276014795323 := by
  unfold tailWord_3061522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915720203659033793798705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74441920543090756783463213 27915720203659033793798705)
  ·
    refine ⟨20936790152744275345349029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27915720203659033793798705 20936790152744275345349029)
    ·
      refine ⟨3925648153639551627252943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20936790152744275345349029 3925648153639551627252943)
      ·
        refine ⟨5888472230459327440879415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925648153639551627252943 5888472230459327440879415)
        ·
          refine ⟨8832708345688991161319123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888472230459327440879415 8832708345688991161319123)
          ·
            refine ⟨13249062518533486741978685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832708345688991161319123 13249062518533486741978685)
            ·
              refine ⟨4968398444450057528242007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13249062518533486741978685 4968398444450057528242007)
              ·
                refine ⟨7452597666675086292363011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968398444450057528242007 7452597666675086292363011)
                ·
                  refine ⟨11178896500012629438544517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452597666675086292363011 11178896500012629438544517)
                  ·
                    refine ⟨2096043093752368019727097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11178896500012629438544517 2096043093752368019727097)
                    ·
                      refine ⟨1572032320314276014795323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096043093752368019727097 1572032320314276014795323)
                      ·
                        rfl

theorem cell23_3061522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3061522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061522 prefixEnd_3061522 := by exact prefixLift 3061522
  have htrace : WordTrace (prefixWord ++ tailWord_3061522) baseStart_3061522 baseEnd_3061522 := by
    simpa [prefixWord, tailWord_3061522, baseEnd_3061522] using wordTrace_append hprefix tailTrace_3061522
  have hstable : (prefixWord ++ tailWord_3061522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061522).length < 2 ^ (prefixWord ++ tailWord_3061522).sum := by decide
  have hdescent : baseEnd_3061522 < baseStart_3061522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061541 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_3061541 : Nat := 118140960795 + 3061541 * 2 ^ 59
def prefixEnd_3061541 : Nat := 4983230072969 + 3 ^ 40 * 3061541 * 2
def baseEnd_3061541 : Nat := 524014025482237146819245

theorem tailTrace_3061541 : CollatzResearch.WordTrace tailWord_3061541 prefixEnd_3061541 524014025482237146819245 := by
  unfold tailWord_3061541
  simp only [CollatzResearch.WordTrace]
  refine ⟨111663573801567301420136477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74442382534378200946757651 111663573801567301420136477)
  ·
    refine ⟨41873840175587738032551179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111663573801567301420136477 41873840175587738032551179)
    ·
      refine ⟨62810760263381607048826769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41873840175587738032551179 62810760263381607048826769)
      ·
        refine ⟨47108070197536205286620077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62810760263381607048826769 47108070197536205286620077)
        ·
          refine ⟨17665526324076076982482529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47108070197536205286620077 17665526324076076982482529)
          ·
            refine ⟨13249144743057057736861897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17665526324076076982482529 13249144743057057736861897)
            ·
              refine ⟨9936858557292793302646423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13249144743057057736861897 9936858557292793302646423)
              ·
                refine ⟨14905287835939189953969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936858557292793302646423 14905287835939189953969635)
                ·
                  refine ⟨22357931753908784930954453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14905287835939189953969635 22357931753908784930954453)
                  ·
                    refine ⟨524014025482237146819245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22357931753908784930954453 524014025482237146819245)
                    ·
                      rfl

theorem cell23_3061541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_3061541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061541 prefixEnd_3061541 := by exact prefixLift 3061541
  have htrace : WordTrace (prefixWord ++ tailWord_3061541) baseStart_3061541 baseEnd_3061541 := by
    simpa [prefixWord, tailWord_3061541, baseEnd_3061541] using wordTrace_append hprefix tailTrace_3061541
  have hstable : (prefixWord ++ tailWord_3061541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061541).length < 2 ^ (prefixWord ++ tailWord_3061541).sum := by decide
  have hdescent : baseEnd_3061541 < baseStart_3061541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061578 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_3061578 : Nat := 118140960795 + 3061578 * 2 ^ 59
def prefixEnd_3061578 : Nat := 4983230072969 + 3 ^ 40 * 3061578 * 2
def baseEnd_3061578 : Nat := 1572061075230927795695065

theorem tailTrace_3061578 : CollatzResearch.WordTrace tailWord_3061578 prefixEnd_3061578 1572061075230927795695065 := by
  unfold tailWord_3061578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916230825608314184808347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74443282201622171159488925 27916230825608314184808347)
  ·
    refine ⟨41874346238412471277212521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27916230825608314184808347 41874346238412471277212521)
    ·
      refine ⟨31405759678809353457909391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41874346238412471277212521 31405759678809353457909391)
      ·
        refine ⟨47108639518214030186864087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31405759678809353457909391 47108639518214030186864087)
        ·
          refine ⟨70662959277321045280296131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47108639518214030186864087 70662959277321045280296131)
          ·
            refine ⟨105994438915981567920444197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70662959277321045280296131 105994438915981567920444197)
            ·
              refine ⟨19873957296746543985083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105994438915981567920444197 19873957296746543985083287)
              ·
                refine ⟨29810935945119815977624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19873957296746543985083287 29810935945119815977624931)
                ·
                  refine ⟨44716403917679723966437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29810935945119815977624931 44716403917679723966437397)
                  ·
                    refine ⟨2096081433641237060926753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44716403917679723966437397 2096081433641237060926753)
                    ·
                      refine ⟨1572061075230927795695065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096081433641237060926753 1572061075230927795695065)
                      ·
                        rfl

theorem cell23_3061578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_3061578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061578 prefixEnd_3061578 := by exact prefixLift 3061578
  have htrace : WordTrace (prefixWord ++ tailWord_3061578) baseStart_3061578 baseEnd_3061578 := by
    simpa [prefixWord, tailWord_3061578, baseEnd_3061578] using wordTrace_append hprefix tailTrace_3061578
  have hstable : (prefixWord ++ tailWord_3061578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061578).length < 2 ^ (prefixWord ++ tailWord_3061578).sum := by decide
  have hdescent : baseEnd_3061578 < baseStart_3061578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061605 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_3061605 : Nat := 118140960795 + 3061605 * 2 ^ 59
def prefixEnd_3061605 : Nat := 4983230072969 + 3 ^ 40 * 3061605 * 2
def baseEnd_3061605 : Nat := 524024979736199730019147

theorem tailTrace_3061605 : CollatzResearch.WordTrace tailWord_3061605 prefixEnd_3061605 524024979736199730019147 := by
  unfold tailWord_3061605
  simp only [CollatzResearch.WordTrace]
  refine ⟨111665908073335440350466269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74443938715556960233644179 111665908073335440350466269)
  ·
    refine ⟨41874715527500790131424851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111665908073335440350466269 41874715527500790131424851)
    ·
      refine ⟨62812073291251185197137277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41874715527500790131424851 62812073291251185197137277)
      ·
        refine ⟨23554527484219194448926479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62812073291251185197137277 23554527484219194448926479)
        ·
          refine ⟨35331791226328791673389719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23554527484219194448926479 35331791226328791673389719)
          ·
            refine ⟨52997686839493187510084579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35331791226328791673389719 52997686839493187510084579)
            ·
              refine ⟨79496530259239781265126869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52997686839493187510084579 79496530259239781265126869)
              ·
                refine ⟨1863199927950932373401411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79496530259239781265126869 1863199927950932373401411)
                ·
                  refine ⟨2794799891926398560102117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863199927950932373401411 2794799891926398560102117)
                  ·
                    refine ⟨524024979736199730019147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794799891926398560102117 524024979736199730019147)
                    ·
                      rfl

theorem cell23_3061605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_3061605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061605 prefixEnd_3061605 := by exact prefixLift 3061605
  have htrace : WordTrace (prefixWord ++ tailWord_3061605) baseStart_3061605 baseEnd_3061605 := by
    simpa [prefixWord, tailWord_3061605, baseEnd_3061605] using wordTrace_append hprefix tailTrace_3061605
  have hstable : (prefixWord ++ tailWord_3061605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061605).length < 2 ^ (prefixWord ++ tailWord_3061605).sum := by decide
  have hdescent : baseEnd_3061605 < baseStart_3061605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061641 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_3061641 : Nat := 118140960795 + 3061641 * 2 ^ 59
def prefixEnd_3061641 : Nat := 4983230072969 + 3 ^ 40 * 3061641 * 2
def baseEnd_3061641 : Nat := 1572093424512161049207275

theorem tailTrace_3061641 : CollatzResearch.WordTrace tailWord_3061641 prefixEnd_3061641 1572093424512161049207275 := by
  unfold tailWord_3061641
  simp only [CollatzResearch.WordTrace]
  refine ⟨111667221101205018498776777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74444814067470012332517851 111667221101205018498776777)
  ·
    refine ⟨83750415825903763874082583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111667221101205018498776777 83750415825903763874082583)
    ·
      refine ⟨125625623738855645811123875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83750415825903763874082583 125625623738855645811123875)
      ·
        refine ⟨188438435608283468716685813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125625623738855645811123875 188438435608283468716685813)
        ·
          refine ⟨17666103338276575192189295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188438435608283468716685813 17666103338276575192189295)
          ·
            refine ⟨26499155007414862788283943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17666103338276575192189295 26499155007414862788283943)
            ·
              refine ⟨39748732511122294182425915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26499155007414862788283943 39748732511122294182425915)
              ·
                refine ⟨59623098766683441273638873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39748732511122294182425915 59623098766683441273638873)
                ·
                  refine ⟨44717324075012580955229155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59623098766683441273638873 44717324075012580955229155)
                  ·
                    refine ⟨67075986112518871432843733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44717324075012580955229155 67075986112518871432843733)
                    ·
                      refine ⟨1572093424512161049207275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67075986112518871432843733 1572093424512161049207275)
                      ·
                        rfl

theorem cell23_3061641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_3061641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061641 prefixEnd_3061641 := by exact prefixLift 3061641
  have htrace : WordTrace (prefixWord ++ tailWord_3061641) baseStart_3061641 baseEnd_3061641 := by
    simpa [prefixWord, tailWord_3061641, baseEnd_3061641] using wordTrace_append hprefix tailTrace_3061641
  have hstable : (prefixWord ++ tailWord_3061641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061641).length < 2 ^ (prefixWord ++ tailWord_3061641).sum := by decide
  have hdescent : baseEnd_3061641 < baseStart_3061641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061655 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_3061655 : Nat := 118140960795 + 3061655 * 2 ^ 59
def prefixEnd_3061655 : Nat := 4983230072969 + 3 ^ 40 * 3061655 * 2
def baseEnd_3061655 : Nat := 1572100613241323994432211

theorem tailTrace_3061655 : CollatzResearch.WordTrace tailWord_3061655 prefixEnd_3061655 1572100613241323994432211 := by
  unfold tailWord_3061655
  simp only [CollatzResearch.WordTrace]
  refine ⟨111667731723154298889786419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74445154482102865926524279 111667731723154298889786419)
  ·
    refine ⟨167501597584731448334679629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111667731723154298889786419 167501597584731448334679629)
    ·
      refine ⟨62813099094274293125504861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167501597584731448334679629 62813099094274293125504861)
      ·
        refine ⟨23554912160352859922064323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62813099094274293125504861 23554912160352859922064323)
        ·
          refine ⟨35332368240529289883096485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23554912160352859922064323 35332368240529289883096485)
          ·
            refine ⟨6624819045099241853080591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35332368240529289883096485 6624819045099241853080591)
            ·
              refine ⟨9937228567648862779620887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624819045099241853080591 9937228567648862779620887)
              ·
                refine ⟨14905842851473294169431331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937228567648862779620887 14905842851473294169431331)
                ·
                  refine ⟨22358764277209941254146997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14905842851473294169431331 22358764277209941254146997)
                  ·
                    refine ⟨2096134150988431992576281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22358764277209941254146997 2096134150988431992576281)
                    ·
                      refine ⟨1572100613241323994432211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096134150988431992576281 1572100613241323994432211)
                      ·
                        rfl

theorem cell23_3061655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_3061655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061655 prefixEnd_3061655 := by exact prefixLift 3061655
  have htrace : WordTrace (prefixWord ++ tailWord_3061655) baseStart_3061655 baseEnd_3061655 := by
    simpa [prefixWord, tailWord_3061655, baseEnd_3061655] using wordTrace_append hprefix tailTrace_3061655
  have hstable : (prefixWord ++ tailWord_3061655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061655).length < 2 ^ (prefixWord ++ tailWord_3061655).sum := by decide
  have hdescent : baseEnd_3061655 < baseStart_3061655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061688 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3061688 : Nat := 118140960795 + 3061688 * 2 ^ 59
def prefixEnd_3061688 : Nat := 4983230072969 + 3 ^ 40 * 3061688 * 2
def baseEnd_3061688 : Nat := 1572117558102922365319559

theorem tailTrace_3061688 : CollatzResearch.WordTrace tailWord_3061688 prefixEnd_3061688 1572117558102922365319559 := by
  unfold tailWord_3061688
  simp only [CollatzResearch.WordTrace]
  refine ⟨55834467666017372762868859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74445956888023163683825145 55834467666017372762868859)
  ·
    refine ⟨83751701499026059144303289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55834467666017372762868859 83751701499026059144303289)
    ·
      refine ⟨62813776124269544358227467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83751701499026059144303289 62813776124269544358227467)
      ·
        refine ⟨94220664186404316537341201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62813776124269544358227467 94220664186404316537341201)
        ·
          refine ⟨70665498139803237403005901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94220664186404316537341201 70665498139803237403005901)
          ·
            refine ⟨26499561802426214026127213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70665498139803237403005901 26499561802426214026127213)
            ·
              refine ⟨9937335675909830259797705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26499561802426214026127213 9937335675909830259797705)
              ·
                refine ⟨7453001756932372694848279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9937335675909830259797705 7453001756932372694848279)
                ·
                  refine ⟨11179502635398559042272419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453001756932372694848279 11179502635398559042272419)
                  ·
                    refine ⟨16769253953097838563408629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11179502635398559042272419 16769253953097838563408629)
                    ·
                      refine ⟨1572117558102922365319559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16769253953097838563408629 1572117558102922365319559)
                      ·
                        rfl

theorem cell23_3061688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3061688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061688 prefixEnd_3061688 := by exact prefixLift 3061688
  have htrace : WordTrace (prefixWord ++ tailWord_3061688) baseStart_3061688 baseEnd_3061688 := by
    simpa [prefixWord, tailWord_3061688, baseEnd_3061688] using wordTrace_append hprefix tailTrace_3061688
  have hstable : (prefixWord ++ tailWord_3061688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061688).length < 2 ^ (prefixWord ++ tailWord_3061688).sum := by decide
  have hdescent : baseEnd_3061688 < baseStart_3061688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061708 : List Nat := [2, 2, 1, 4, 1, 3, 1, 9]
def baseStart_3061708 : Nat := 118140960795 + 3061708 * 2 ^ 59
def prefixEnd_3061708 : Nat := 4983230072969 + 3 ^ 40 * 3061708 * 2
def baseEnd_3061708 : Nat := 58226956582074529150721

theorem tailTrace_3061708 : CollatzResearch.WordTrace tailWord_3061708 prefixEnd_3061708 58226956582074529150721 := by
  unfold tailWord_3061708
  simp only [CollatzResearch.WordTrace]
  refine ⟨55834832395981144470732889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74446443194641525960977185 55834832395981144470732889)
  ·
    refine ⟨41876124296985858353049667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55834832395981144470732889 41876124296985858353049667)
    ·
      refine ⟨62814186445478787529574501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41876124296985858353049667 62814186445478787529574501)
      ·
        refine ⟨11777659958527272661795219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62814186445478787529574501 11777659958527272661795219)
        ·
          refine ⟨17666489937790908992692829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11777659958527272661795219 17666489937790908992692829)
          ·
            refine ⟨6624933726671590872259811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17666489937790908992692829 6624933726671590872259811)
            ·
              refine ⟨9937400590007386308389717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624933726671590872259811 9937400590007386308389717)
              ·
                refine ⟨58226956582074529150721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9937400590007386308389717 58226956582074529150721)
                ·
                  rfl

theorem cell23_3061708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 9].length) (baseStart_3061708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061708 prefixEnd_3061708 := by exact prefixLift 3061708
  have htrace : WordTrace (prefixWord ++ tailWord_3061708) baseStart_3061708 baseEnd_3061708 := by
    simpa [prefixWord, tailWord_3061708, baseEnd_3061708] using wordTrace_append hprefix tailTrace_3061708
  have hstable : (prefixWord ++ tailWord_3061708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061708).length < 2 ^ (prefixWord ++ tailWord_3061708).sum := by decide
  have hdescent : baseEnd_3061708 < baseStart_3061708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061725 : List Nat := [1, 4, 3, 1, 3, 2, 9]
def baseStart_3061725 : Nat := 118140960795 + 3061725 * 2 ^ 59
def prefixEnd_3061725 : Nat := 4983230072969 + 3 ^ 40 * 3061725 * 2
def baseEnd_3061725 : Nat := 19409093294902947167369

theorem tailTrace_3061725 : CollatzResearch.WordTrace tailWord_3061725 prefixEnd_3061725 19409093294902947167369 := by
  unfold tailWord_3061725
  simp only [CollatzResearch.WordTrace]
  refine ⟨111670284832900700844834629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74446856555267133896556419 111670284832900700844834629)
  ·
    refine ⟨20938178406168881408406493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111670284832900700844834629 20938178406168881408406493)
    ·
      refine ⟨7851816902313330528152435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20938178406168881408406493 7851816902313330528152435)
      ·
        refine ⟨11777725353469995792228653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7851816902313330528152435 11777725353469995792228653)
        ·
          refine ⟨4416647007551248422085745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11777725353469995792228653 4416647007551248422085745)
          ·
            refine ⟨3312485255663436316564309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416647007551248422085745 3312485255663436316564309)
            ·
              refine ⟨19409093294902947167369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3312485255663436316564309 19409093294902947167369)
              ·
                rfl

theorem cell23_3061725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 9].length) (baseStart_3061725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061725 prefixEnd_3061725 := by exact prefixLift 3061725
  have htrace : WordTrace (prefixWord ++ tailWord_3061725) baseStart_3061725 baseEnd_3061725 := by
    simpa [prefixWord, tailWord_3061725, baseEnd_3061725] using wordTrace_append hprefix tailTrace_3061725
  have hstable : (prefixWord ++ tailWord_3061725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061725).length < 2 ^ (prefixWord ++ tailWord_3061725).sum := by decide
  have hdescent : baseEnd_3061725 < baseStart_3061725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061738 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3061738 : Nat := 118140960795 + 3061738 * 2 ^ 59
def prefixEnd_3061738 : Nat := 4983230072969 + 3 ^ 40 * 3061738 * 2
def baseEnd_3061738 : Nat := 524047744045215723231443

theorem tailTrace_3061738 : CollatzResearch.WordTrace tailWord_3061738 prefixEnd_3061738 524047744045215723231443 := by
  unfold tailWord_3061738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27917689745463401016264467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74447172654569069376705245 27917689745463401016264467)
  ·
    refine ⟨41876534618195101524396701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27917689745463401016264467 41876534618195101524396701)
    ·
      refine ⟨15703700481823163071648763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41876534618195101524396701 15703700481823163071648763)
      ·
        refine ⟨23555550722734744607473145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15703700481823163071648763 23555550722734744607473145)
        ·
          refine ⟨17666663042051058455604859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23555550722734744607473145 17666663042051058455604859)
          ·
            refine ⟨26499994563076587683407289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17666663042051058455604859 26499994563076587683407289)
            ·
              refine ⟨19874995922307440762555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26499994563076587683407289 19874995922307440762555467)
              ·
                refine ⟨29812493883461161143833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19874995922307440762555467 29812493883461161143833201)
                ·
                  refine ⟨22359370412595870857874901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29812493883461161143833201 22359370412595870857874901)
                  ·
                    refine ⟨524047744045215723231443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22359370412595870857874901 524047744045215723231443)
                    ·
                      rfl

theorem cell23_3061738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3061738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061738 prefixEnd_3061738 := by exact prefixLift 3061738
  have htrace : WordTrace (prefixWord ++ tailWord_3061738) baseStart_3061738 baseEnd_3061738 := by
    simpa [prefixWord, tailWord_3061738, baseEnd_3061738] using wordTrace_append hprefix tailTrace_3061738
  have hstable : (prefixWord ++ tailWord_3061738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061738).length < 2 ^ (prefixWord ++ tailWord_3061738).sum := by decide
  have hdescent : baseEnd_3061738 < baseStart_3061738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061773 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3061773 : Nat := 118140960795 + 3061773 * 2 ^ 59
def prefixEnd_3061773 : Nat := 4983230072969 + 3 ^ 40 * 3061773 * 2
def baseEnd_3061773 : Nat := 1572161203958554532756669

theorem tailTrace_3061773 : CollatzResearch.WordTrace tailWord_3061773 prefixEnd_3061773 1572161203958554532756669 := by
  unfold tailWord_3061773
  simp only [CollatzResearch.WordTrace]
  refine ⟨111672035536726805042581973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74448023691151203361721315 111672035536726805042581973)
  ·
    refine ⟨2617313332892034493185515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 111672035536726805042581973 2617313332892034493185515)
    ·
      refine ⟨3925969999338051739778273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2617313332892034493185515 3925969999338051739778273)
      ·
        refine ⟨2944477499503538804833705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925969999338051739778273 2944477499503538804833705)
        ·
          refine ⟨2208358124627654103625279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944477499503538804833705 2208358124627654103625279)
          ·
            refine ⟨3312537186941481155437919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208358124627654103625279 3312537186941481155437919)
            ·
              refine ⟨4968805780412221733156879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312537186941481155437919 4968805780412221733156879)
              ·
                refine ⟨7453208670618332599735319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968805780412221733156879 7453208670618332599735319)
                ·
                  refine ⟨11179813005927498899602979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453208670618332599735319 11179813005927498899602979)
                  ·
                    refine ⟨16769719508891248349404469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11179813005927498899602979 16769719508891248349404469)
                    ·
                      refine ⟨1572161203958554532756669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16769719508891248349404469 1572161203958554532756669)
                      ·
                        rfl

theorem cell23_3061773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3061773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061773 prefixEnd_3061773 := by exact prefixLift 3061773
  have htrace : WordTrace (prefixWord ++ tailWord_3061773) baseStart_3061773 baseEnd_3061773 := by
    simpa [prefixWord, tailWord_3061773, baseEnd_3061773] using wordTrace_append hprefix tailTrace_3061773
  have hstable : (prefixWord ++ tailWord_3061773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061773).length < 2 ^ (prefixWord ++ tailWord_3061773).sum := by decide
  have hdescent : baseEnd_3061773 < baseStart_3061773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061809 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_3061809 : Nat := 118140960795 + 3061809 * 2 ^ 59
def prefixEnd_3061809 : Nat := 4983230072969 + 3 ^ 40 * 3061809 * 2
def baseEnd_3061809 : Nat := 1572179689262116391906503

theorem tailTrace_3061809 : CollatzResearch.WordTrace tailWord_3061809 prefixEnd_3061809 1572179689262116391906503 := by
  unfold tailWord_3061809
  simp only [CollatzResearch.WordTrace]
  refine ⟨111673348564596383190892481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74448899043064255460594987 111673348564596383190892481)
  ·
    refine ⟨83755011423447287393169361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111673348564596383190892481 83755011423447287393169361)
    ·
      refine ⟨62816258567585465544877021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83755011423447287393169361 62816258567585465544877021)
      ·
        refine ⟨23556096962844549579328883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62816258567585465544877021 23556096962844549579328883)
        ·
          refine ⟨35334145444266824368993325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23556096962844549579328883 35334145444266824368993325)
          ·
            refine ⟨13250304541600059138372497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35334145444266824368993325 13250304541600059138372497)
            ·
              refine ⟨9937728406200044353779373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250304541600059138372497 9937728406200044353779373)
              ·
                refine ⟨3726648152325016632667265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9937728406200044353779373 3726648152325016632667265)
                ·
                  refine ⟨2794986114243762474500449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3726648152325016632667265 2794986114243762474500449)
                  ·
                    refine ⟨2096239585682821855875337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2794986114243762474500449 2096239585682821855875337)
                    ·
                      refine ⟨1572179689262116391906503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096239585682821855875337 1572179689262116391906503)
                      ·
                        rfl

theorem cell23_3061809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_3061809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061809 prefixEnd_3061809 := by exact prefixLift 3061809
  have htrace : WordTrace (prefixWord ++ tailWord_3061809) baseStart_3061809 baseEnd_3061809 := by
    simpa [prefixWord, tailWord_3061809, baseEnd_3061809] using wordTrace_append hprefix tailTrace_3061809
  have hstable : (prefixWord ++ tailWord_3061809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061809).length < 2 ^ (prefixWord ++ tailWord_3061809).sum := by decide
  have hdescent : baseEnd_3061809 < baseStart_3061809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061835 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 5, 2]
def baseStart_3061835 : Nat := 118140960795 + 3061835 * 2 ^ 59
def prefixEnd_3061835 : Nat := 4983230072969 + 3 ^ 40 * 3061835 * 2
def baseEnd_3061835 : Nat := 1572193039759133290181383

theorem tailTrace_3061835 : CollatzResearch.WordTrace tailWord_3061835 prefixEnd_3061835 1572193039759133290181383 := by
  unfold tailWord_3061835
  simp only [CollatzResearch.WordTrace]
  refine ⟨111674296862502189631338959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74449531241668126420892639 111674296862502189631338959)
  ·
    refine ⟨167511445293753284447008439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111674296862502189631338959 167511445293753284447008439)
    ·
      refine ⟨251267167940629926670512659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167511445293753284447008439 251267167940629926670512659)
      ·
        refine ⟨376900751910944890005768989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251267167940629926670512659 376900751910944890005768989)
        ·
          refine ⟨141337781966604333752163371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376900751910944890005768989 141337781966604333752163371)
          ·
            refine ⟨212006672949906500628245057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141337781966604333752163371 212006672949906500628245057)
            ·
              refine ⟨159005004712429875471183793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212006672949906500628245057 159005004712429875471183793)
              ·
                refine ⟨119253753534322406603387845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159005004712429875471183793 119253753534322406603387845)
                ·
                  refine ⟨22360078787685451238135221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119253753534322406603387845 22360078787685451238135221)
                  ·
                    refine ⟨2096257386345511053575177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22360078787685451238135221 2096257386345511053575177)
                    ·
                      refine ⟨1572193039759133290181383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096257386345511053575177 1572193039759133290181383)
                      ·
                        rfl

theorem cell23_3061835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5, 2].length) (baseStart_3061835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061835 prefixEnd_3061835 := by exact prefixLift 3061835
  have htrace : WordTrace (prefixWord ++ tailWord_3061835) baseStart_3061835 baseEnd_3061835 := by
    simpa [prefixWord, tailWord_3061835, baseEnd_3061835] using wordTrace_append hprefix tailTrace_3061835
  have hstable : (prefixWord ++ tailWord_3061835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061835).length < 2 ^ (prefixWord ++ tailWord_3061835).sum := by decide
  have hdescent : baseEnd_3061835 < baseStart_3061835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3061975 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3061975 : Nat := 118140960795 + 3061975 * 2 ^ 59
def prefixEnd_3061975 : Nat := 4983230072969 + 3 ^ 40 * 3061975 * 2
def baseEnd_3061975 : Nat := 1572264927050762742430739

theorem tailTrace_3061975 : CollatzResearch.WordTrace tailWord_3061975 prefixEnd_3061975 1572264927050762742430739 := by
  unfold tailWord_3061975
  simp only [CollatzResearch.WordTrace]
  refine ⟨111679403081994993541435379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74452935387996662360956919 111679403081994993541435379)
  ·
    refine ⟨167519104622992490312153069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111679403081994993541435379 167519104622992490312153069)
    ·
      refine ⟨62819664233622183867057401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167519104622992490312153069 62819664233622183867057401)
      ·
        refine ⟨47114748175216637900293051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62819664233622183867057401 47114748175216637900293051)
        ·
          refine ⟨70672122262824956850439577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47114748175216637900293051 70672122262824956850439577)
          ·
            refine ⟨53004091697118717637829683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70672122262824956850439577 53004091697118717637829683)
            ·
              refine ⟨79506137545678076456744525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53004091697118717637829683 79506137545678076456744525)
              ·
                refine ⟨29814801579629278671279197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79506137545678076456744525 29814801579629278671279197)
                ·
                  refine ⟨11180550592360979501729699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29814801579629278671279197 11180550592360979501729699)
                  ·
                    refine ⟨16770825888541469252594549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11180550592360979501729699 16770825888541469252594549)
                    ·
                      refine ⟨1572264927050762742430739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16770825888541469252594549 1572264927050762742430739)
                      ·
                        rfl

theorem cell23_3061975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3061975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3061975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3061975 prefixEnd_3061975 := by exact prefixLift 3061975
  have htrace : WordTrace (prefixWord ++ tailWord_3061975) baseStart_3061975 baseEnd_3061975 := by
    simpa [prefixWord, tailWord_3061975, baseEnd_3061975] using wordTrace_append hprefix tailTrace_3061975
  have hstable : (prefixWord ++ tailWord_3061975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3061975).length < 2 ^ (prefixWord ++ tailWord_3061975).sum := by decide
  have hdescent : baseEnd_3061975 < baseStart_3061975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3061975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062006 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3062006 : Nat := 118140960795 + 3062006 * 2 ^ 59
def prefixEnd_3062006 : Nat := 4983230072969 + 3 ^ 40 * 3062006 * 2
def baseEnd_3062006 : Nat := 1572280844951052121143097

theorem tailTrace_3062006 : CollatzResearch.WordTrace tailWord_3062006 prefixEnd_3062006 1572280844951052121143097 := by
  unfold tailWord_3062006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980033359055167864738367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74453689163255123890542581 6980033359055167864738367)
  ·
    refine ⟨10470050038582751797107551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6980033359055167864738367 10470050038582751797107551)
    ·
      refine ⟨15705075057874127695661327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10470050038582751797107551 15705075057874127695661327)
      ·
        refine ⟨23557612586811191543491991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705075057874127695661327 23557612586811191543491991)
        ·
          refine ⟨35336418880216787315237987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557612586811191543491991 35336418880216787315237987)
          ·
            refine ⟨53004628320325180972856981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35336418880216787315237987 53004628320325180972856981)
            ·
              refine ⟨2484591952515242858102671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53004628320325180972856981 2484591952515242858102671)
              ·
                refine ⟨3726887928772864287154007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484591952515242858102671 3726887928772864287154007)
                ·
                  refine ⟨5590331893159296430731011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726887928772864287154007 5590331893159296430731011)
                  ·
                    refine ⟨8385497839738944646096517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590331893159296430731011 8385497839738944646096517)
                    ·
                      refine ⟨1572280844951052121143097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8385497839738944646096517 1572280844951052121143097)
                      ·
                        rfl

theorem cell23_3062006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3062006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062006 prefixEnd_3062006 := by exact prefixLift 3062006
  have htrace : WordTrace (prefixWord ++ tailWord_3062006) baseStart_3062006 baseEnd_3062006 := by
    simpa [prefixWord, tailWord_3062006, baseEnd_3062006] using wordTrace_append hprefix tailTrace_3062006
  have hstable : (prefixWord ++ tailWord_3062006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062006).length < 2 ^ (prefixWord ++ tailWord_3062006).sum := by decide
  have hdescent : baseEnd_3062006 < baseStart_3062006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062035 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_3062035 : Nat := 118140960795 + 3062035 * 2 ^ 59
def prefixEnd_3062035 : Nat := 4983230072969 + 3 ^ 40 * 3062035 * 2
def baseEnd_3062035 : Nat := 1572295735890032507680463

theorem tailTrace_3062035 : CollatzResearch.WordTrace tailWord_3062035 prefixEnd_3062035 1572295735890032507680463 := by
  unfold tailWord_3062035
  simp only [CollatzResearch.WordTrace]
  refine ⟨111681591461777623788619559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74454394307851749192413039 111681591461777623788619559)
  ·
    refine ⟨167522387192666435682929339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111681591461777623788619559 167522387192666435682929339)
    ·
      refine ⟨251283580788999653524394009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167522387192666435682929339 251283580788999653524394009)
      ·
        refine ⟨188462685591749740143295507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251283580788999653524394009 188462685591749740143295507)
        ·
          refine ⟨282694028387624610214943261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188462685591749740143295507 282694028387624610214943261)
          ·
            refine ⟨106010260645359228830603723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282694028387624610214943261 106010260645359228830603723)
            ·
              refine ⟨159015390968038843245905585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106010260645359228830603723 159015390968038843245905585)
              ·
                refine ⟨119261543226029132434429189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159015390968038843245905585 119261543226029132434429189)
                ·
                  refine ⟨22361539354880462331455473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119261543226029132434429189 22361539354880462331455473)
                  ·
                    refine ⟨16771154516160346748591605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22361539354880462331455473 16771154516160346748591605)
                    ·
                      refine ⟨1572295735890032507680463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16771154516160346748591605 1572295735890032507680463)
                      ·
                        rfl

theorem cell23_3062035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_3062035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062035 prefixEnd_3062035 := by exact prefixLift 3062035
  have htrace : WordTrace (prefixWord ++ tailWord_3062035) baseStart_3062035 baseEnd_3062035 := by
    simpa [prefixWord, tailWord_3062035, baseEnd_3062035] using wordTrace_append hprefix tailTrace_3062035
  have hstable : (prefixWord ++ tailWord_3062035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062035).length < 2 ^ (prefixWord ++ tailWord_3062035).sum := by decide
  have hdescent : baseEnd_3062035 < baseStart_3062035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062039 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3062039 : Nat := 118140960795 + 3062039 * 2 ^ 59
def prefixEnd_3062039 : Nat := 4983230072969 + 3 ^ 40 * 3062039 * 2
def baseEnd_3062039 : Nat := 1572297789812650492030445

theorem tailTrace_3062039 : CollatzResearch.WordTrace tailWord_3062039 prefixEnd_3062039 1572297789812650492030445 := by
  unfold tailWord_3062039
  simp only [CollatzResearch.WordTrace]
  refine ⟨111681737353763132471765171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74454491569175421647843447 111681737353763132471765171)
  ·
    refine ⟨167522606030644698707647757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111681737353763132471765171 167522606030644698707647757)
    ·
      refine ⟨62820977261491762015367909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167522606030644698707647757 62820977261491762015367909)
      ·
        refine ⟨11778933236529705377881483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62820977261491762015367909 11778933236529705377881483)
        ·
          refine ⟨17668399854794558066822225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778933236529705377881483 17668399854794558066822225)
          ·
            refine ⟨13251299891095918550116669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17668399854794558066822225 13251299891095918550116669)
            ·
              refine ⟨4969237459160969456293751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13251299891095918550116669 4969237459160969456293751)
              ·
                refine ⟨7453856188741454184440627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969237459160969456293751 7453856188741454184440627)
                ·
                  refine ⟨11180784283112181276660941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453856188741454184440627 11180784283112181276660941)
                  ·
                    refine ⟨4192794106167067978747853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11180784283112181276660941 4192794106167067978747853)
                    ·
                      refine ⟨1572297789812650492030445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4192794106167067978747853 1572297789812650492030445)
                      ·
                        rfl

theorem cell23_3062039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3062039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062039 prefixEnd_3062039 := by exact prefixLift 3062039
  have htrace : WordTrace (prefixWord ++ tailWord_3062039) baseStart_3062039 baseEnd_3062039 := by
    simpa [prefixWord, tailWord_3062039, baseEnd_3062039] using wordTrace_append hprefix tailTrace_3062039
  have hstable : (prefixWord ++ tailWord_3062039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062039).length < 2 ^ (prefixWord ++ tailWord_3062039).sum := by decide
  have hdescent : baseEnd_3062039 < baseStart_3062039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062046 : List Nat := [4, 3, 2, 1, 1, 1, 4, 7]
def baseStart_3062046 : Nat := 118140960795 + 3062046 * 2 ^ 59
def prefixEnd_3062046 : Nat := 4983230072969 + 3 ^ 40 * 3062046 * 2
def baseEnd_3062046 : Nat := 58233384599156739431219

theorem tailTrace_3062046 : CollatzResearch.WordTrace tailWord_3062046 prefixEnd_3062046 58233384599156739431219 := by
  unfold tailWord_3062046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960249083092221583408749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74454661776491848444846661 13960249083092221583408749)
  ·
    refine ⟨5235093406159583093778281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13960249083092221583408749 5235093406159583093778281)
    ·
      refine ⟨3926320054619687320333711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5235093406159583093778281 3926320054619687320333711)
      ·
        refine ⟨5889480081929530980500567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926320054619687320333711 5889480081929530980500567)
        ·
          refine ⟨8834220122894296470750851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5889480081929530980500567 8834220122894296470750851)
          ·
            refine ⟨13251330184341444706126277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834220122894296470750851 13251330184341444706126277)
            ·
              refine ⟨2484624409564020882398677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13251330184341444706126277 2484624409564020882398677)
              ·
                refine ⟨58233384599156739431219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2484624409564020882398677 58233384599156739431219)
                ·
                  rfl

theorem cell23_3062046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_3062046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062046 prefixEnd_3062046 := by exact prefixLift 3062046
  have htrace : WordTrace (prefixWord ++ tailWord_3062046) baseStart_3062046 baseEnd_3062046 := by
    simpa [prefixWord, tailWord_3062046, baseEnd_3062046] using wordTrace_append hprefix tailTrace_3062046
  have hstable : (prefixWord ++ tailWord_3062046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062046).length < 2 ^ (prefixWord ++ tailWord_3062046).sum := by decide
  have hdescent : baseEnd_3062046 < baseStart_3062046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062049 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3062049 : Nat := 118140960795 + 3062049 * 2 ^ 59
def prefixEnd_3062049 : Nat := 4983230072969 + 3 ^ 40 * 3062049 * 2
def baseEnd_3062049 : Nat := 1572302924619195452905399

theorem tailTrace_3062049 : CollatzResearch.WordTrace tailWord_3062049 prefixEnd_3062049 1572302924619195452905399 := by
  unfold tailWord_3062049
  simp only [CollatzResearch.WordTrace]
  refine ⟨111682102083726904179629201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74454734722484602786419467 111682102083726904179629201)
  ·
    refine ⟨83761576562795178134721901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111682102083726904179629201 83761576562795178134721901)
    ·
      refine ⟨31410591211048191800520713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83761576562795178134721901 31410591211048191800520713)
      ·
        refine ⟨23557943408286143850390535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31410591211048191800520713 23557943408286143850390535)
        ·
          refine ⟨35336915112429215775585803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557943408286143850390535 35336915112429215775585803)
          ·
            refine ⟨53005372668643823663378705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35336915112429215775585803 53005372668643823663378705)
            ·
              refine ⟨39754029501482867747534029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53005372668643823663378705 39754029501482867747534029)
              ·
                refine ⟨14907761063056075405325261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39754029501482867747534029 14907761063056075405325261)
                ·
                  refine ⟨5590410398646028276996973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14907761063056075405325261 5590410398646028276996973)
                  ·
                    refine ⟨2096403899492260603873865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5590410398646028276996973 2096403899492260603873865)
                    ·
                      refine ⟨1572302924619195452905399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096403899492260603873865 1572302924619195452905399)
                      ·
                        rfl

theorem cell23_3062049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3062049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062049 prefixEnd_3062049 := by exact prefixLift 3062049
  have htrace : WordTrace (prefixWord ++ tailWord_3062049) baseStart_3062049 baseEnd_3062049 := by
    simpa [prefixWord, tailWord_3062049, baseEnd_3062049] using wordTrace_append hprefix tailTrace_3062049
  have hstable : (prefixWord ++ tailWord_3062049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062049).length < 2 ^ (prefixWord ++ tailWord_3062049).sum := by decide
  have hdescent : baseEnd_3062049 < baseStart_3062049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062052 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3062052 : Nat := 118140960795 + 3062052 * 2 ^ 59
def prefixEnd_3062052 : Nat := 4983230072969 + 3 ^ 40 * 3062052 * 2
def baseEnd_3062052 : Nat := 1572304465061158941167885

theorem tailTrace_3062052 : CollatzResearch.WordTrace tailWord_3062052 prefixEnd_3062052 1572304465061158941167885 := by
  unfold tailWord_3062052
  simp only [CollatzResearch.WordTrace]
  refine ⟨55841105751358017845994205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74454807668477357127992273 55841105751358017845994205)
  ·
    refine ⟨20940414656759256692247827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55841105751358017845994205 20940414656759256692247827)
    ·
      refine ⟨31410621985138885038371741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20940414656759256692247827 31410621985138885038371741)
      ·
        refine ⟨11778983244427081889389403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31410621985138885038371741 11778983244427081889389403)
        ·
          refine ⟨17668474866640622834084105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778983244427081889389403 17668474866640622834084105)
          ·
            refine ⟨13251356149980467125563079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17668474866640622834084105 13251356149980467125563079)
            ·
              refine ⟨19877034224970700688344619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13251356149980467125563079 19877034224970700688344619)
              ·
                refine ⟨29815551337456051032516929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877034224970700688344619 29815551337456051032516929)
                ·
                  refine ⟨22361663503092038274387697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29815551337456051032516929 22361663503092038274387697)
                  ·
                    refine ⟨16771247627319028705790773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22361663503092038274387697 16771247627319028705790773)
                    ·
                      refine ⟨1572304465061158941167885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16771247627319028705790773 1572304465061158941167885)
                      ·
                        rfl

theorem cell23_3062052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3062052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062052 prefixEnd_3062052 := by exact prefixLift 3062052
  have htrace : WordTrace (prefixWord ++ tailWord_3062052) baseStart_3062052 baseEnd_3062052 := by
    simpa [prefixWord, tailWord_3062052, baseEnd_3062052] using wordTrace_append hprefix tailTrace_3062052
  have hstable : (prefixWord ++ tailWord_3062052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062052).length < 2 ^ (prefixWord ++ tailWord_3062052).sum := by decide
  have hdescent : baseEnd_3062052 < baseStart_3062052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062092 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3062092 : Nat := 118140960795 + 3062092 * 2 ^ 59
def prefixEnd_3062092 : Nat := 4983230072969 + 3 ^ 40 * 3062092 * 2
def baseEnd_3062092 : Nat := 1572325004287338784667701

theorem tailTrace_3062092 : CollatzResearch.WordTrace tailWord_3062092 prefixEnd_3062092 1572325004287338784667701 := by
  unfold tailWord_3062092
  simp only [CollatzResearch.WordTrace]
  refine ⟨55841835211285561261722265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74455780281714081682296353 55841835211285561261722265)
  ·
    refine ⟨41881376408464170946291699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55841835211285561261722265 41881376408464170946291699)
    ·
      refine ⟨62822064612696256419437549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41881376408464170946291699 62822064612696256419437549)
      ·
        refine ⟨23558274229761096157289081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62822064612696256419437549 23558274229761096157289081)
        ·
          refine ⟨17668705672320822117966811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23558274229761096157289081 17668705672320822117966811)
          ·
            refine ⟨26503058508481233176950217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17668705672320822117966811 26503058508481233176950217)
            ·
              refine ⟨19877293881360924882712663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26503058508481233176950217 19877293881360924882712663)
              ·
                refine ⟨29815940822041387324068995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877293881360924882712663 29815940822041387324068995)
                ·
                  refine ⟨44723911233062080986103493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29815940822041387324068995 44723911233062080986103493)
                  ·
                    refine ⟨8385733356199140184894405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44723911233062080986103493 8385733356199140184894405)
                    ·
                      refine ⟨1572325004287338784667701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8385733356199140184894405 1572325004287338784667701)
                      ·
                        rfl

theorem cell23_3062092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3062092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062092 prefixEnd_3062092 := by exact prefixLift 3062092
  have htrace : WordTrace (prefixWord ++ tailWord_3062092) baseStart_3062092 baseEnd_3062092 := by
    simpa [prefixWord, tailWord_3062092, baseEnd_3062092] using wordTrace_append hprefix tailTrace_3062092
  have hstable : (prefixWord ++ tailWord_3062092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062092).length < 2 ^ (prefixWord ++ tailWord_3062092).sum := by decide
  have hdescent : baseEnd_3062092 < baseStart_3062092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062139 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 5, 2]
def baseStart_3062139 : Nat := 118140960795 + 3062139 * 2 ^ 59
def prefixEnd_3062139 : Nat := 4983230072969 + 3 ^ 40 * 3062139 * 2
def baseEnd_3062139 : Nat := 1572349137878100100779985

theorem tailTrace_3062139 : CollatzResearch.WordTrace tailWord_3062139 prefixEnd_3062139 1572349137878100100779985 := by
  unfold tailWord_3062139
  simp only [CollatzResearch.WordTrace]
  refine ⟨111685384653400849550405471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74456923102267233033603647 111685384653400849550405471)
  ·
    refine ⟨167528076980101274325608207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111685384653400849550405471 167528076980101274325608207)
    ·
      refine ⟨251292115470151911488412311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167528076980101274325608207 251292115470151911488412311)
      ·
        refine ⟨376938173205227867232618467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251292115470151911488412311 376938173205227867232618467)
        ·
          refine ⟨565407259807841800848927701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376938173205227867232618467 565407259807841800848927701)
          ·
            refine ⟨13251732651746292207396743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 565407259807841800848927701 13251732651746292207396743)
            ·
              refine ⟨19877598977619438311095115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13251732651746292207396743 19877598977619438311095115)
              ·
                refine ⟨29816398466429157466642673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877598977619438311095115 29816398466429157466642673)
                ·
                  refine ⟨22362298849821868099982005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29816398466429157466642673 22362298849821868099982005)
                  ·
                    refine ⟨2096465517170800134373313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22362298849821868099982005 2096465517170800134373313)
                    ·
                      refine ⟨1572349137878100100779985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096465517170800134373313 1572349137878100100779985)
                      ·
                        rfl

theorem cell23_3062139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5, 2].length) (baseStart_3062139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062139 prefixEnd_3062139 := by exact prefixLift 3062139
  have htrace : WordTrace (prefixWord ++ tailWord_3062139) baseStart_3062139 baseEnd_3062139 := by
    simpa [prefixWord, tailWord_3062139, baseEnd_3062139] using wordTrace_append hprefix tailTrace_3062139
  have hstable : (prefixWord ++ tailWord_3062139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062139).length < 2 ^ (prefixWord ++ tailWord_3062139).sum := by decide
  have hdescent : baseEnd_3062139 < baseStart_3062139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062169 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 6, 2]
def baseStart_3062169 : Nat := 118140960795 + 3062169 * 2 ^ 59
def prefixEnd_3062169 : Nat := 4983230072969 + 3 ^ 40 * 3062169 * 2
def baseEnd_3062169 : Nat := 1572364542297734983404847

theorem tailTrace_3062169 : CollatzResearch.WordTrace tailWord_3062169 prefixEnd_3062169 1572364542297734983404847 := by
  unfold tailWord_3062169
  simp only [CollatzResearch.WordTrace]
  refine ⟨111686478843292164673997561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74457652562194776449331707 111686478843292164673997561)
  ·
    refine ⟨83764859132469123505498171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111686478843292164673997561 83764859132469123505498171)
    ·
      refine ⟨125647288698703685258247257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83764859132469123505498171 125647288698703685258247257)
      ·
        refine ⟨94235466524027763943685443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125647288698703685258247257 94235466524027763943685443)
        ·
          refine ⟨141353199786041645915528165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94235466524027763943685443 141353199786041645915528165)
          ·
            refine ⟨26503724959882808609161531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141353199786041645915528165 26503724959882808609161531)
            ·
              refine ⟨39755587439824212913742297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26503724959882808609161531 39755587439824212913742297)
              ·
                refine ⟨29816690579868159685306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39755587439824212913742297 29816690579868159685306723)
                ·
                  refine ⟨44725035869802239527960085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29816690579868159685306723 44725035869802239527960085)
                  ·
                    refine ⟨2096486056396979977873129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44725035869802239527960085 2096486056396979977873129)
                    ·
                      refine ⟨1572364542297734983404847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096486056396979977873129 1572364542297734983404847)
                      ·
                        rfl

theorem cell23_3062169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_3062169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062169 prefixEnd_3062169 := by exact prefixLift 3062169
  have htrace : WordTrace (prefixWord ++ tailWord_3062169) baseStart_3062169 baseEnd_3062169 := by
    simpa [prefixWord, tailWord_3062169, baseEnd_3062169] using wordTrace_append hprefix tailTrace_3062169
  have hstable : (prefixWord ++ tailWord_3062169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062169).length < 2 ^ (prefixWord ++ tailWord_3062169).sum := by decide
  have hdescent : baseEnd_3062169 < baseStart_3062169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062259 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4]
def baseStart_3062259 : Nat := 118140960795 + 3062259 * 2 ^ 59
def prefixEnd_3062259 : Nat := 4983230072969 + 3 ^ 40 * 3062259 * 2
def baseEnd_3062259 : Nat := 1572410755556639631279433

theorem tailTrace_3062259 : CollatzResearch.WordTrace tailWord_3062259 prefixEnd_3062259 1572410755556639631279433 := by
  unfold tailWord_3062259
  simp only [CollatzResearch.WordTrace]
  refine ⟨111689761412966110044773831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74459840941977406696515887 111689761412966110044773831)
  ·
    refine ⟨167534642119449165067160747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111689761412966110044773831 167534642119449165067160747)
    ·
      refine ⟨251301963179173747600741121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167534642119449165067160747 251301963179173747600741121)
      ·
        refine ⟨188476472384380310700555841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251301963179173747600741121 188476472384380310700555841)
        ·
          refine ⟨141357354288285233025416881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188476472384380310700555841 141357354288285233025416881)
          ·
            refine ⟨106018015716213924769062661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141357354288285233025416881 106018015716213924769062661)
            ·
              refine ⟨19878377946790110894199249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106018015716213924769062661 19878377946790110894199249)
              ·
                refine ⟨14908783460092583170649437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19878377946790110894199249 14908783460092583170649437)
                ·
                  refine ⟨5590793797534718688993539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14908783460092583170649437 5590793797534718688993539)
                  ·
                    refine ⟨8386190696302078033490309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590793797534718688993539 8386190696302078033490309)
                    ·
                      refine ⟨1572410755556639631279433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8386190696302078033490309 1572410755556639631279433)
                      ·
                        rfl

theorem cell23_3062259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_3062259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062259 prefixEnd_3062259 := by exact prefixLift 3062259
  have htrace : WordTrace (prefixWord ++ tailWord_3062259) baseStart_3062259 baseEnd_3062259 := by
    simpa [prefixWord, tailWord_3062259, baseEnd_3062259] using wordTrace_append hprefix tailTrace_3062259
  have hstable : (prefixWord ++ tailWord_3062259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062259).length < 2 ^ (prefixWord ++ tailWord_3062259).sum := by decide
  have hdescent : baseEnd_3062259 < baseStart_3062259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062269 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_3062269 : Nat := 118140960795 + 3062269 * 2 ^ 59
def prefixEnd_3062269 : Nat := 4983230072969 + 3 ^ 40 * 3062269 * 2
def baseEnd_3062269 : Nat := 524138630121061530718129

theorem tailTrace_3062269 : CollatzResearch.WordTrace tailWord_3062269 prefixEnd_3062269 524138630121061530718129 := by
  unfold tailWord_3062269
  simp only [CollatzResearch.WordTrace]
  refine ⟨111690126142929881752637861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74460084095286587835091907 111690126142929881752637861)
  ·
    refine ⟨20941898651799352828619599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111690126142929881752637861 20941898651799352828619599)
    ·
      refine ⟨31412847977699029242929399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20941898651799352828619599 31412847977699029242929399)
      ·
        refine ⟨47119271966548543864394099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31412847977699029242929399 47119271966548543864394099)
        ·
          refine ⟨70678907949822815796591149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47119271966548543864394099 70678907949822815796591149)
          ·
            refine ⟨26504590481183555923721681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70678907949822815796591149 26504590481183555923721681)
            ·
              refine ⟨19878442860887666942791261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26504590481183555923721681 19878442860887666942791261)
              ·
                refine ⟨7454416072832875103546723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19878442860887666942791261 7454416072832875103546723)
                ·
                  refine ⟨11181624109249312655320085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454416072832875103546723 11181624109249312655320085)
                  ·
                    refine ⟨524138630121061530718129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11181624109249312655320085 524138630121061530718129)
                    ·
                      rfl

theorem cell23_3062269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_3062269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062269 prefixEnd_3062269 := by exact prefixLift 3062269
  have htrace : WordTrace (prefixWord ++ tailWord_3062269) baseStart_3062269 baseEnd_3062269 := by
    simpa [prefixWord, tailWord_3062269, baseEnd_3062269] using wordTrace_append hprefix tailTrace_3062269
  have hstable : (prefixWord ++ tailWord_3062269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062269).length < 2 ^ (prefixWord ++ tailWord_3062269).sum := by decide
  have hdescent : baseEnd_3062269 < baseStart_3062269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062273 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3062273 : Nat := 118140960795 + 3062273 * 2 ^ 59
def prefixEnd_3062273 : Nat := 4983230072969 + 3 ^ 40 * 3062273 * 2
def baseEnd_3062273 : Nat := 524139314761934192168123

theorem tailTrace_3062273 : CollatzResearch.WordTrace tailWord_3062273 prefixEnd_3062273 524139314761934192168123 := by
  unfold tailWord_3062273
  simp only [CollatzResearch.WordTrace]
  refine ⟨111690272034915390435783473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74460181356610260290522315 111690272034915390435783473)
  ·
    refine ⟨83767704026186542826837605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111690272034915390435783473 83767704026186542826837605)
    ·
      refine ⟨15706444504909976780032051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83767704026186542826837605 15706444504909976780032051)
      ·
        refine ⟨23559666757364965170048077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15706444504909976780032051 23559666757364965170048077)
        ·
          refine ⟨8834875034011861938768029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23559666757364965170048077 8834875034011861938768029)
          ·
            refine ⟨3313078137754448227038011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8834875034011861938768029 3313078137754448227038011)
            ·
              refine ⟨4969617206631672340557017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313078137754448227038011 4969617206631672340557017)
              ·
                refine ⟨3727212904973754255417763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4969617206631672340557017 3727212904973754255417763)
                ·
                  refine ⟨5590819357460631383126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727212904973754255417763 5590819357460631383126645)
                  ·
                    refine ⟨524139314761934192168123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5590819357460631383126645 524139314761934192168123)
                    ·
                      rfl

theorem cell23_3062273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3062273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062273 prefixEnd_3062273 := by exact prefixLift 3062273
  have htrace : WordTrace (prefixWord ++ tailWord_3062273) baseStart_3062273 baseEnd_3062273 := by
    simpa [prefixWord, tailWord_3062273, baseEnd_3062273] using wordTrace_append hprefix tailTrace_3062273
  have hstable : (prefixWord ++ tailWord_3062273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062273).length < 2 ^ (prefixWord ++ tailWord_3062273).sum := by decide
  have hdescent : baseEnd_3062273 < baseStart_3062273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062286 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3062286 : Nat := 118140960795 + 3062286 * 2 ^ 59
def prefixEnd_3062286 : Nat := 4983230072969 + 3 ^ 40 * 3062286 * 2
def baseEnd_3062286 : Nat := 524141539844770341880603

theorem tailTrace_3062286 : CollatzResearch.WordTrace tailWord_3062286 prefixEnd_3062286 524141539844770341880603 := by
  unfold tailWord_3062286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961343272983536707000839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74460497455912195770671141 13961343272983536707000839)
  ·
    refine ⟨20942014909475305060501259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13961343272983536707000839 20942014909475305060501259)
    ·
      refine ⟨31413022364212957590751889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20942014909475305060501259 31413022364212957590751889)
      ·
        refine ⟨23559766773159718193063917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31413022364212957590751889 23559766773159718193063917)
        ·
          refine ⟨8834912539934894322398969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23559766773159718193063917 8834912539934894322398969)
          ·
            refine ⟨6626184404951170741799227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8834912539934894322398969 6626184404951170741799227)
            ·
              refine ⟨9939276607426756112698841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626184404951170741799227 9939276607426756112698841)
              ·
                refine ⟨7454457455570067084524131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9939276607426756112698841 7454457455570067084524131)
                ·
                  refine ⟨11181686183355100626786197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454457455570067084524131 11181686183355100626786197)
                  ·
                    refine ⟨524141539844770341880603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11181686183355100626786197 524141539844770341880603)
                    ·
                      rfl

theorem cell23_3062286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3062286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062286 prefixEnd_3062286 := by exact prefixLift 3062286
  have htrace : WordTrace (prefixWord ++ tailWord_3062286) baseStart_3062286 baseEnd_3062286 := by
    simpa [prefixWord, tailWord_3062286, baseEnd_3062286] using wordTrace_append hprefix tailTrace_3062286
  have hstable : (prefixWord ++ tailWord_3062286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062286).length < 2 ^ (prefixWord ++ tailWord_3062286).sum := by decide
  have hdescent : baseEnd_3062286 < baseStart_3062286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062293 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_3062293 : Nat := 118140960795 + 3062293 * 2 ^ 59
def prefixEnd_3062293 : Nat := 4983230072969 + 3 ^ 40 * 3062293 * 2
def baseEnd_3062293 : Nat := 1572428213898892498254277

theorem tailTrace_3062293 : CollatzResearch.WordTrace tailWord_3062293 prefixEnd_3062293 1572428213898892498254277 := by
  unfold tailWord_3062293
  simp only [CollatzResearch.WordTrace]
  refine ⟨111691001494842933851511533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74460667663228622567674355 111691001494842933851511533)
  ·
    refine ⟨41884125560566100194316825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111691001494842933851511533 41884125560566100194316825)
    ·
      refine ⟨31413094170424575145737619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41884125560566100194316825 31413094170424575145737619)
      ·
        refine ⟨47119641255636862718606429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31413094170424575145737619 47119641255636862718606429)
        ·
          refine ⟨17669865470863823519477411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47119641255636862718606429 17669865470863823519477411)
          ·
            refine ⟨26504798206295735279216117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669865470863823519477411 26504798206295735279216117)
            ·
              refine ⟨2484824831840225182426511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26504798206295735279216117 2484824831840225182426511)
              ·
                refine ⟨3727237247760337773639767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484824831840225182426511 3727237247760337773639767)
                ·
                  refine ⟨5590855871640506660459651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727237247760337773639767 5590855871640506660459651)
                  ·
                    refine ⟨8386283807460759990689477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590855871640506660459651 8386283807460759990689477)
                    ·
                      refine ⟨1572428213898892498254277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8386283807460759990689477 1572428213898892498254277)
                      ·
                        rfl

theorem cell23_3062293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_3062293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062293 prefixEnd_3062293 := by exact prefixLift 3062293
  have htrace : WordTrace (prefixWord ++ tailWord_3062293) baseStart_3062293 baseEnd_3062293 := by
    simpa [prefixWord, tailWord_3062293, baseEnd_3062293] using wordTrace_append hprefix tailTrace_3062293
  have hstable : (prefixWord ++ tailWord_3062293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062293).length < 2 ^ (prefixWord ++ tailWord_3062293).sum := by decide
  have hdescent : baseEnd_3062293 < baseStart_3062293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062296 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3062296 : Nat := 118140960795 + 3062296 * 2 ^ 59
def prefixEnd_3062296 : Nat := 4983230072969 + 3 ^ 40 * 3062296 * 2
def baseEnd_3062296 : Nat := 1572429754340855986516763

theorem tailTrace_3062296 : CollatzResearch.WordTrace tailWord_3062296 prefixEnd_3062296 1572429754340855986516763 := by
  unfold tailWord_3062296
  simp only [CollatzResearch.WordTrace]
  refine ⟨55845555456916032681935371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74460740609221376909247161 55845555456916032681935371)
  ·
    refine ⟨83768333185374049022903057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55845555456916032681935371 83768333185374049022903057)
    ·
      refine ⟨62826249889030536767177293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83768333185374049022903057 62826249889030536767177293)
      ·
        refine ⟨23559843708386451287691485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62826249889030536767177293 23559843708386451287691485)
        ·
          refine ⟨8834941390644919232884307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23559843708386451287691485 8834941390644919232884307)
          ·
            refine ⟨13252412085967378849326461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834941390644919232884307 13252412085967378849326461)
            ·
              refine ⟨4969654532237767068497423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13252412085967378849326461 4969654532237767068497423)
              ·
                refine ⟨7454481798356650602746135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969654532237767068497423 7454481798356650602746135)
                ·
                  refine ⟨11181722697534975904119203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454481798356650602746135 11181722697534975904119203)
                  ·
                    refine ⟨16772584046302463856178805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11181722697534975904119203 16772584046302463856178805)
                    ·
                      refine ⟨1572429754340855986516763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16772584046302463856178805 1572429754340855986516763)
                      ·
                        rfl

theorem cell23_3062296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3062296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062296 prefixEnd_3062296 := by exact prefixLift 3062296
  have htrace : WordTrace (prefixWord ++ tailWord_3062296) baseStart_3062296 baseEnd_3062296 := by
    simpa [prefixWord, tailWord_3062296, baseEnd_3062296] using wordTrace_append hprefix tailTrace_3062296
  have hstable : (prefixWord ++ tailWord_3062296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062296).length < 2 ^ (prefixWord ++ tailWord_3062296).sum := by decide
  have hdescent : baseEnd_3062296 < baseStart_3062296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062304 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3062304 : Nat := 118140960795 + 3062304 * 2 ^ 59
def prefixEnd_3062304 : Nat := 4983230072969 + 3 ^ 40 * 3062304 * 2
def baseEnd_3062304 : Nat := 1572433862186091955216727

theorem tailTrace_3062304 : CollatzResearch.WordTrace tailWord_3062304 prefixEnd_3062304 1572433862186091955216727 := by
  unfold tailWord_3062304
  simp only [CollatzResearch.WordTrace]
  refine ⟨55845701348901541365080983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74460935131868721820107977 55845701348901541365080983)
  ·
    refine ⟨83768552023352312047621475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55845701348901541365080983 83768552023352312047621475)
    ·
      refine ⟨125652828035028468071432213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83768552023352312047621475 125652828035028468071432213)
      ·
        refine ⟨5889976314141959440848385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125652828035028468071432213 5889976314141959440848385)
        ·
          refine ⟨4417482235606469580636289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5889976314141959440848385 4417482235606469580636289)
          ·
            refine ⟨3313111676704852185477217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4417482235606469580636289 3313111676704852185477217)
            ·
              refine ⟨2484833757528639139107913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3313111676704852185477217 2484833757528639139107913)
              ·
                refine ⟨1863625318146479354330935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484833757528639139107913 1863625318146479354330935)
                ·
                  refine ⟨2795437977219719031496403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863625318146479354330935 2795437977219719031496403)
                  ·
                    refine ⟨4193156965829578547244605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2795437977219719031496403 4193156965829578547244605)
                    ·
                      refine ⟨1572433862186091955216727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193156965829578547244605 1572433862186091955216727)
                      ·
                        rfl

theorem cell23_3062304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3062304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062304 prefixEnd_3062304 := by exact prefixLift 3062304
  have htrace : WordTrace (prefixWord ++ tailWord_3062304) baseStart_3062304 baseEnd_3062304 := by
    simpa [prefixWord, tailWord_3062304, baseEnd_3062304] using wordTrace_append hprefix tailTrace_3062304
  have hstable : (prefixWord ++ tailWord_3062304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062304).length < 2 ^ (prefixWord ++ tailWord_3062304).sum := by decide
  have hdescent : baseEnd_3062304 < baseStart_3062304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062329 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_3062329 : Nat := 118140960795 + 3062329 * 2 ^ 59
def prefixEnd_3062329 : Nat := 4983230072969 + 3 ^ 40 * 3062329 * 2
def baseEnd_3062329 : Nat := 524148899734151452468037

theorem tailTrace_3062329 : CollatzResearch.WordTrace tailWord_3062329 prefixEnd_3062329 524148899734151452468037 := by
  unfold tailWord_3062329
  simp only [CollatzResearch.WordTrace]
  refine ⟨111692314522712511999822041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74461543015141674666548027 111692314522712511999822041)
  ·
    refine ⟨83769235892034383999866531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111692314522712511999822041 83769235892034383999866531)
    ·
      refine ⟨125653853838051575999799797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83769235892034383999866531 125653853838051575999799797)
      ·
        refine ⟨11780048797317335249981231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125653853838051575999799797 11780048797317335249981231)
        ·
          refine ⟨17670073195976002874971847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11780048797317335249981231 17670073195976002874971847)
          ·
            refine ⟨26505109793964004312457771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17670073195976002874971847 26505109793964004312457771)
            ·
              refine ⟨39757664690946006468686657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26505109793964004312457771 39757664690946006468686657)
              ·
                refine ⟨29818248518209504851514993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39757664690946006468686657 29818248518209504851514993)
                ·
                  refine ⟨22363686388657128638636245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29818248518209504851514993 22363686388657128638636245)
                  ·
                    refine ⟨524148899734151452468037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22363686388657128638636245 524148899734151452468037)
                    ·
                      rfl

theorem cell23_3062329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_3062329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062329 prefixEnd_3062329 := by exact prefixLift 3062329
  have htrace : WordTrace (prefixWord ++ tailWord_3062329) baseStart_3062329 baseEnd_3062329 := by
    simpa [prefixWord, tailWord_3062329, baseEnd_3062329] using wordTrace_append hprefix tailTrace_3062329
  have hstable : (prefixWord ++ tailWord_3062329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062329).length < 2 ^ (prefixWord ++ tailWord_3062329).sum := by decide
  have hdescent : baseEnd_3062329 < baseStart_3062329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062359 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3062359 : Nat := 118140960795 + 3062359 * 2 ^ 59
def prefixEnd_3062359 : Nat := 4983230072969 + 3 ^ 40 * 3062359 * 2
def baseEnd_3062359 : Nat := 524154034540696413342991

theorem tailTrace_3062359 : CollatzResearch.WordTrace tailWord_3062359 prefixEnd_3062359 524154034540696413342991 := by
  unfold tailWord_3062359
  simp only [CollatzResearch.WordTrace]
  refine ⟨111693408712603827123414131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74462272475069218082276087 111693408712603827123414131)
  ·
    refine ⟨167540113068905740685121197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111693408712603827123414131 167540113068905740685121197)
    ·
      refine ⟨62827542400839652756920449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167540113068905740685121197 62827542400839652756920449)
      ·
        refine ⟨47120656800629739567690337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62827542400839652756920449 47120656800629739567690337)
        ·
          refine ⟨35340492600472304675767753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47120656800629739567690337 35340492600472304675767753)
          ·
            refine ⟨26505369450354228506825815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35340492600472304675767753 26505369450354228506825815)
            ·
              refine ⟨39758054175531342760238723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26505369450354228506825815 39758054175531342760238723)
              ·
                refine ⟨59637081263297014140358085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39758054175531342760238723 59637081263297014140358085)
                ·
                  refine ⟨11181952736868190151317141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59637081263297014140358085 11181952736868190151317141)
                  ·
                    refine ⟨524154034540696413342991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11181952736868190151317141 524154034540696413342991)
                    ·
                      rfl

theorem cell23_3062359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3062359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062359 prefixEnd_3062359 := by exact prefixLift 3062359
  have htrace : WordTrace (prefixWord ++ tailWord_3062359) baseStart_3062359 baseEnd_3062359 := by
    simpa [prefixWord, tailWord_3062359, baseEnd_3062359] using wordTrace_append hprefix tailTrace_3062359
  have hstable : (prefixWord ++ tailWord_3062359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062359).length < 2 ^ (prefixWord ++ tailWord_3062359).sum := by decide
  have hdescent : baseEnd_3062359 < baseStart_3062359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062379 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_3062379 : Nat := 118140960795 + 3062379 * 2 ^ 59
def prefixEnd_3062379 : Nat := 4983230072969 + 3 ^ 40 * 3062379 * 2
def baseEnd_3062379 : Nat := 1572472373235179161778881

theorem tailTrace_3062379 : CollatzResearch.WordTrace tailWord_3062379 prefixEnd_3062379 1572472373235179161778881 := by
  unfold tailWord_3062379
  simp only [CollatzResearch.WordTrace]
  refine ⟨111694138172531370539142191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74462758781687580359428127 111694138172531370539142191)
  ·
    refine ⟨167541207258797055808713287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111694138172531370539142191 167541207258797055808713287)
    ·
      refine ⟨251311810888195583713069931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167541207258797055808713287 251311810888195583713069931)
      ·
        refine ⟨376967716332293375569604897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251311810888195583713069931 376967716332293375569604897)
        ·
          refine ⟨282725787249220031677203673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376967716332293375569604897 282725787249220031677203673)
          ·
            refine ⟨212044340436915023757902755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282725787249220031677203673 212044340436915023757902755)
            ·
              refine ⟨318066510655372535636854133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212044340436915023757902755 318066510655372535636854133)
              ·
                refine ⟨29818735373941175215955075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318066510655372535636854133 29818735373941175215955075)
                ·
                  refine ⟨44728103060911762823932613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29818735373941175215955075 44728103060911762823932613)
                  ·
                    refine ⟨8386519323920955529487365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44728103060911762823932613 8386519323920955529487365)
                    ·
                      refine ⟨1572472373235179161778881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8386519323920955529487365 1572472373235179161778881)
                      ·
                        rfl

theorem cell23_3062379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_3062379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062379 prefixEnd_3062379 := by exact prefixLift 3062379
  have htrace : WordTrace (prefixWord ++ tailWord_3062379) baseStart_3062379 baseEnd_3062379 := by
    simpa [prefixWord, tailWord_3062379, baseEnd_3062379] using wordTrace_append hprefix tailTrace_3062379
  have hstable : (prefixWord ++ tailWord_3062379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062379).length < 2 ^ (prefixWord ++ tailWord_3062379).sum := by decide
  have hdescent : baseEnd_3062379 < baseStart_3062379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062383 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 4, 2]
def baseStart_3062383 : Nat := 118140960795 + 3062383 * 2 ^ 59
def prefixEnd_3062383 : Nat := 4983230072969 + 3 ^ 40 * 3062383 * 2
def baseEnd_3062383 : Nat := 1572474427157797146128863

theorem tailTrace_3062383 : CollatzResearch.WordTrace tailWord_3062383 prefixEnd_3062383 1572474427157797146128863 := by
  unfold tailWord_3062383
  simp only [CollatzResearch.WordTrace]
  refine ⟨111694284064516879222287803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74462856043011252814858535 111694284064516879222287803)
  ·
    refine ⟨167541426096775318833431705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111694284064516879222287803 167541426096775318833431705)
    ·
      refine ⟨125656069572581489125073779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167541426096775318833431705 125656069572581489125073779)
      ·
        refine ⟨188484104358872233687610669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125656069572581489125073779 188484104358872233687610669)
        ·
          refine ⟨70681539134577087632854001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188484104358872233687610669 70681539134577087632854001)
          ·
            refine ⟨53011154350932815724640501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70681539134577087632854001 53011154350932815724640501)
            ·
              refine ⟨4969795720399951474185047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53011154350932815724640501 4969795720399951474185047)
              ·
                refine ⟨7454693580599927211277571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969795720399951474185047 7454693580599927211277571)
                ·
                  refine ⟨11182040370899890816916357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454693580599927211277571 11182040370899890816916357)
                  ·
                    refine ⟨2096632569543729528171817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11182040370899890816916357 2096632569543729528171817)
                    ·
                      refine ⟨1572474427157797146128863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096632569543729528171817 1572474427157797146128863)
                      ·
                        rfl

theorem cell23_3062383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4, 2].length) (baseStart_3062383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062383 prefixEnd_3062383 := by exact prefixLift 3062383
  have htrace : WordTrace (prefixWord ++ tailWord_3062383) baseStart_3062383 baseEnd_3062383 := by
    simpa [prefixWord, tailWord_3062383, baseEnd_3062383] using wordTrace_append hprefix tailTrace_3062383
  have hstable : (prefixWord ++ tailWord_3062383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062383).length < 2 ^ (prefixWord ++ tailWord_3062383).sum := by decide
  have hdescent : baseEnd_3062383 < baseStart_3062383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062436 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3062436 : Nat := 118140960795 + 3062436 * 2 ^ 59
def prefixEnd_3062436 : Nat := 4983230072969 + 3 ^ 40 * 3062436 * 2
def baseEnd_3062436 : Nat := 524167213877495146255373

theorem tailTrace_3062436 : CollatzResearch.WordTrace tailWord_3062436 prefixEnd_3062436 524167213877495146255373 := by
  unfold tailWord_3062436
  simp only [CollatzResearch.WordTrace]
  refine ⟨55848108566662434636983581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74464144755549912849311441 55848108566662434636983581)
  ·
    refine ⟨20943040712498412988868843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55848108566662434636983581 20943040712498412988868843)
    ·
      refine ⟨31414561068747619483303265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20943040712498412988868843 31414561068747619483303265)
      ·
        refine ⟨23560920801560714612477449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31414561068747619483303265 23560920801560714612477449)
        ·
          refine ⟨17670690601170535959358087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23560920801560714612477449 17670690601170535959358087)
          ·
            refine ⟨26506035901755803939037131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17670690601170535959358087 26506035901755803939037131)
            ·
              refine ⟨39759053852633705908555697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26506035901755803939037131 39759053852633705908555697)
              ·
                refine ⟨29819290389475279431416773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39759053852633705908555697 29819290389475279431416773)
                ·
                  refine ⟨5591116948026614893390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29819290389475279431416773 5591116948026614893390645)
                  ·
                    refine ⟨524167213877495146255373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591116948026614893390645 524167213877495146255373)
                    ·
                      rfl

theorem cell23_3062436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3062436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062436 prefixEnd_3062436 := by exact prefixLift 3062436
  have htrace : WordTrace (prefixWord ++ tailWord_3062436) baseStart_3062436 baseEnd_3062436 := by
    simpa [prefixWord, tailWord_3062436, baseEnd_3062436] using wordTrace_append hprefix tailTrace_3062436
  have hstable : (prefixWord ++ tailWord_3062436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062436).length < 2 ^ (prefixWord ++ tailWord_3062436).sum := by decide
  have hdescent : baseEnd_3062436 < baseStart_3062436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062453 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3062453 : Nat := 118140960795 + 3062453 * 2 ^ 59
def prefixEnd_3062453 : Nat := 4983230072969 + 3 ^ 40 * 3062453 * 2
def baseEnd_3062453 : Nat := 524170123601203957417847

theorem tailTrace_3062453 : CollatzResearch.WordTrace tailWord_3062453 prefixEnd_3062453 524170123601203957417847 := by
  unfold tailWord_3062453
  simp only [CollatzResearch.WordTrace]
  refine ⟨111696837174263281177336013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74464558116175520784890675 111696837174263281177336013)
  ·
    refine ⟨41886313940348730441501005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111696837174263281177336013 41886313940348730441501005)
    ·
      refine ⟨15707367727630773915562877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41886313940348730441501005 15707367727630773915562877)
      ·
        refine ⟨5890262897861540218336079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15707367727630773915562877 5890262897861540218336079)
        ·
          refine ⟨8835394346792310327504119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890262897861540218336079 8835394346792310327504119)
          ·
            refine ⟨13253091520188465491256179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835394346792310327504119 13253091520188465491256179)
            ·
              refine ⟨19879637280282698236884269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13253091520188465491256179 19879637280282698236884269)
              ·
                refine ⟨7454863980106011838831601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19879637280282698236884269 7454863980106011838831601)
                ·
                  refine ⟨5591147985079508879123701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454863980106011838831601 5591147985079508879123701)
                  ·
                    refine ⟨524170123601203957417847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591147985079508879123701 524170123601203957417847)
                    ·
                      rfl

theorem cell23_3062453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3062453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062453 prefixEnd_3062453 := by exact prefixLift 3062453
  have htrace : WordTrace (prefixWord ++ tailWord_3062453) baseStart_3062453 baseEnd_3062453 := by
    simpa [prefixWord, tailWord_3062453, baseEnd_3062453] using wordTrace_append hprefix tailTrace_3062453
  have hstable : (prefixWord ++ tailWord_3062453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062453).length < 2 ^ (prefixWord ++ tailWord_3062453).sum := by decide
  have hdescent : baseEnd_3062453 < baseStart_3062453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062459 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_3062459 : Nat := 118140960795 + 3062459 * 2 ^ 59
def prefixEnd_3062459 : Nat := 4983230072969 + 3 ^ 40 * 3062459 * 2
def baseEnd_3062459 : Nat := 1572513451687538848778513

theorem tailTrace_3062459 : CollatzResearch.WordTrace tailWord_3062459 prefixEnd_3062459 1572513451687538848778513 := by
  unfold tailWord_3062459
  simp only [CollatzResearch.WordTrace]
  refine ⟨111697056012241544202054431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74464704008161029468036287 111697056012241544202054431)
  ·
    refine ⟨167545584018362316303081647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111697056012241544202054431 167545584018362316303081647)
    ·
      refine ⟨251318376027543474454622471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167545584018362316303081647 251318376027543474454622471)
      ·
        refine ⟨376977564041315211681933707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251318376027543474454622471 376977564041315211681933707)
        ·
          refine ⟨565466346061972817522900561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376977564041315211681933707 565466346061972817522900561)
          ·
            refine ⟨424099759546479613142175421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565466346061972817522900561 424099759546479613142175421)
            ·
              refine ⟨159037409829929854928315783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424099759546479613142175421 159037409829929854928315783)
              ·
                refine ⟨238556114744894782392473675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159037409829929854928315783 238556114744894782392473675)
                ·
                  refine ⟨357834172117342173588710513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238556114744894782392473675 357834172117342173588710513)
                  ·
                    refine ⟨268375629088006630191532885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357834172117342173588710513 268375629088006630191532885)
                    ·
                      refine ⟨1572513451687538848778513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 268375629088006630191532885 1572513451687538848778513)
                      ·
                        rfl

theorem cell23_3062459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_3062459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062459 prefixEnd_3062459 := by exact prefixLift 3062459
  have htrace : WordTrace (prefixWord ++ tailWord_3062459) baseStart_3062459 baseEnd_3062459 := by
    simpa [prefixWord, tailWord_3062459, baseEnd_3062459] using wordTrace_append hprefix tailTrace_3062459
  have hstable : (prefixWord ++ tailWord_3062459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062459).length < 2 ^ (prefixWord ++ tailWord_3062459).sum := by decide
  have hdescent : baseEnd_3062459 < baseStart_3062459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062510 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3062510 : Nat := 118140960795 + 3062510 * 2 ^ 59
def prefixEnd_3062510 : Nat := 4983230072969 + 3 ^ 40 * 3062510 * 2
def baseEnd_3062510 : Nat := 1572539639200918149240779

theorem tailTrace_3062510 : CollatzResearch.WordTrace tailWord_3062510 prefixEnd_3062510 1572539639200918149240779 := by
  unfold tailWord_3062510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13962364516882097489020123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74465944090037853274773989 13962364516882097489020123)
  ·
    refine ⟨20943546775323146233530185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13962364516882097489020123 20943546775323146233530185)
    ·
      refine ⟨15707660081492359675147639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20943546775323146233530185 15707660081492359675147639)
      ·
        refine ⟨23561490122238539512721459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15707660081492359675147639 23561490122238539512721459)
        ·
          refine ⟨35342235183357809269082189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23561490122238539512721459 35342235183357809269082189)
          ·
            refine ⟨13253338193759178475905821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35342235183357809269082189 13253338193759178475905821)
            ·
              refine ⟨4970001822659691928464683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13253338193759178475905821 4970001822659691928464683)
              ·
                refine ⟨7455002733989537892697025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970001822659691928464683 7455002733989537892697025)
                ·
                  refine ⟨5591252050492153419522769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7455002733989537892697025 5591252050492153419522769)
                  ·
                    refine ⟨4193439037869115064642077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591252050492153419522769 4193439037869115064642077)
                    ·
                      refine ⟨1572539639200918149240779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193439037869115064642077 1572539639200918149240779)
                      ·
                        rfl

theorem cell23_3062510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3062510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062510 prefixEnd_3062510 := by exact prefixLift 3062510
  have htrace : WordTrace (prefixWord ++ tailWord_3062510) baseStart_3062510 baseEnd_3062510 := by
    simpa [prefixWord, tailWord_3062510, baseEnd_3062510] using wordTrace_append hprefix tailTrace_3062510
  have hstable : (prefixWord ++ tailWord_3062510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062510).length < 2 ^ (prefixWord ++ tailWord_3062510).sum := by decide
  have hdescent : baseEnd_3062510 < baseStart_3062510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062530 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3062530 : Nat := 118140960795 + 3062530 * 2 ^ 59
def prefixEnd_3062530 : Nat := 4983230072969 + 3 ^ 40 * 3062530 * 2
def baseEnd_3062530 : Nat := 174727767646000896776743

theorem tailTrace_3062530 : CollatzResearch.WordTrace tailWord_3062530 prefixEnd_3062530 174727767646000896776743 := by
  unfold tailWord_3062530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27924911398746080831972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74466430396656215551926029 27924911398746080831972261)
  ·
    refine ⟨5235920887264890155994799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27924911398746080831972261 5235920887264890155994799)
    ·
      refine ⟨7853881330897335233992199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235920887264890155994799 7853881330897335233992199)
      ·
        refine ⟨11780821996346002850988299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7853881330897335233992199 11780821996346002850988299)
        ·
          refine ⟨17671232994519004276482449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11780821996346002850988299 17671232994519004276482449)
          ·
            refine ⟨13253424745889253207361837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17671232994519004276482449 13253424745889253207361837)
            ·
              refine ⟨4970034279708469952760689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13253424745889253207361837 4970034279708469952760689)
              ·
                refine ⟨3727525709781352464570517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970034279708469952760689 3727525709781352464570517)
                ·
                  refine ⟨174727767646000896776743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3727525709781352464570517 174727767646000896776743)
                  ·
                    rfl

theorem cell23_3062530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3062530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062530 prefixEnd_3062530 := by exact prefixLift 3062530
  have htrace : WordTrace (prefixWord ++ tailWord_3062530) baseStart_3062530 baseEnd_3062530 := by
    simpa [prefixWord, tailWord_3062530, baseEnd_3062530] using wordTrace_append hprefix tailTrace_3062530
  have hstable : (prefixWord ++ tailWord_3062530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062530).length < 2 ^ (prefixWord ++ tailWord_3062530).sum := by decide
  have hdescent : baseEnd_3062530 < baseStart_3062530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062560 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_3062560 : Nat := 118140960795 + 3062560 * 2 ^ 59
def prefixEnd_3062560 : Nat := 4983230072969 + 3 ^ 40 * 3062560 * 2
def baseEnd_3062560 : Nat := 524188437744547651205183

theorem tailTrace_3062560 : CollatzResearch.WordTrace tailWord_3062560 prefixEnd_3062560 524188437744547651205183 := by
  unfold tailWord_3062560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55850369892437819225740567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74467159856583758967654089 55850369892437819225740567)
  ·
    refine ⟨83775554838656728838610851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55850369892437819225740567 83775554838656728838610851)
    ·
      refine ⟨125663332257985093257916277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83775554838656728838610851 125663332257985093257916277)
      ·
        refine ⟨11780937399186102492929651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125663332257985093257916277 11780937399186102492929651)
        ·
          refine ⟨17671406098779153739394477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11780937399186102492929651 17671406098779153739394477)
          ·
            refine ⟨6626777287042182652272929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17671406098779153739394477 6626777287042182652272929)
            ·
              refine ⟨4970082965281636989204697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626777287042182652272929 4970082965281636989204697)
              ·
                refine ⟨3727562223961227741903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970082965281636989204697 3727562223961227741903523)
                ·
                  refine ⟨5591343335941841612855285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727562223961227741903523 5591343335941841612855285)
                  ·
                    refine ⟨524188437744547651205183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591343335941841612855285 524188437744547651205183)
                    ·
                      rfl

theorem cell23_3062560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_3062560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062560 prefixEnd_3062560 := by exact prefixLift 3062560
  have htrace : WordTrace (prefixWord ++ tailWord_3062560) baseStart_3062560 baseEnd_3062560 := by
    simpa [prefixWord, tailWord_3062560, baseEnd_3062560] using wordTrace_append hprefix tailTrace_3062560
  have hstable : (prefixWord ++ tailWord_3062560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062560).length < 2 ^ (prefixWord ++ tailWord_3062560).sum := by decide
  have hdescent : baseEnd_3062560 < baseStart_3062560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062563 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 8, 2]
def baseStart_3062563 : Nat := 118140960795 + 3062563 * 2 ^ 59
def prefixEnd_3062563 : Nat := 4983230072969 + 3 ^ 40 * 3062563 * 2
def baseEnd_3062563 : Nat := 1572566853675606441878035

theorem tailTrace_3062563 : CollatzResearch.WordTrace tailWord_3062563 prefixEnd_3062563 1572566853675606441878035 := by
  unfold tailWord_3062563
  simp only [CollatzResearch.WordTrace]
  refine ⟨111700849203864769963840343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74467232802576513309226895 111700849203864769963840343)
  ·
    refine ⟨167551273805797154945760515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111700849203864769963840343 167551273805797154945760515)
    ·
      refine ⟨251326910708695732418640773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167551273805797154945760515 251326910708695732418640773)
      ·
        refine ⟨47123795757880449828495145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251326910708695732418640773 47123795757880449828495145)
        ·
          refine ⟨35342846818410337371371359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47123795757880449828495145 35342846818410337371371359)
          ·
            refine ⟨53014270227615506057057039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35342846818410337371371359 53014270227615506057057039)
            ·
              refine ⟨79521405341423259085585559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53014270227615506057057039 79521405341423259085585559)
              ·
                refine ⟨119282108012134888628378339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79521405341423259085585559 119282108012134888628378339)
                ·
                  refine ⟨178923162018202332942567509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119282108012134888628378339 178923162018202332942567509)
                  ·
                    refine ⟨2096755804900808589170713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 178923162018202332942567509 2096755804900808589170713)
                    ·
                      refine ⟨1572566853675606441878035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096755804900808589170713 1572566853675606441878035)
                      ·
                        rfl

theorem cell23_3062563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_3062563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062563 prefixEnd_3062563 := by exact prefixLift 3062563
  have htrace : WordTrace (prefixWord ++ tailWord_3062563) baseStart_3062563 baseEnd_3062563 := by
    simpa [prefixWord, tailWord_3062563, baseEnd_3062563] using wordTrace_append hprefix tailTrace_3062563
  have hstable : (prefixWord ++ tailWord_3062563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062563).length < 2 ^ (prefixWord ++ tailWord_3062563).sum := by decide
  have hdescent : baseEnd_3062563 < baseStart_3062563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062583 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_3062583 : Nat := 118140960795 + 3062583 * 2 ^ 59
def prefixEnd_3062583 : Nat := 4983230072969 + 3 ^ 40 * 3062583 * 2
def baseEnd_3062583 : Nat := 1572577123288696363627943

theorem tailTrace_3062583 : CollatzResearch.WordTrace tailWord_3062583 prefixEnd_3062583 1572577123288696363627943 := by
  unfold tailWord_3062583
  simp only [CollatzResearch.WordTrace]
  refine ⟨111701578663792313379568403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74467719109194875586378935 111701578663792313379568403)
  ·
    refine ⟨167552367995688470069352605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111701578663792313379568403 167552367995688470069352605)
    ·
      refine ⟨62832137998383176276007227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167552367995688470069352605 62832137998383176276007227)
      ·
        refine ⟨94248206997574764414010841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62832137998383176276007227 94248206997574764414010841)
        ·
          refine ⟨70686155248181073310508131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94248206997574764414010841 70686155248181073310508131)
          ·
            refine ⟨106029232872271609965762197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70686155248181073310508131 106029232872271609965762197)
            ·
              refine ⟨4970120290887731717145103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106029232872271609965762197 4970120290887731717145103)
              ·
                refine ⟨7455180436331597575717655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970120290887731717145103 7455180436331597575717655)
                ·
                  refine ⟨11182770654497396363576483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455180436331597575717655 11182770654497396363576483)
                  ·
                    refine ⟨16774155981746094545364725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11182770654497396363576483 16774155981746094545364725)
                    ·
                      refine ⟨1572577123288696363627943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16774155981746094545364725 1572577123288696363627943)
                      ·
                        rfl

theorem cell23_3062583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_3062583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062583 prefixEnd_3062583 := by exact prefixLift 3062583
  have htrace : WordTrace (prefixWord ++ tailWord_3062583) baseStart_3062583 baseEnd_3062583 := by
    simpa [prefixWord, tailWord_3062583, baseEnd_3062583] using wordTrace_append hprefix tailTrace_3062583
  have hstable : (prefixWord ++ tailWord_3062583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062583).length < 2 ^ (prefixWord ++ tailWord_3062583).sum := by decide
  have hdescent : baseEnd_3062583 < baseStart_3062583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062617 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_3062617 : Nat := 118140960795 + 3062617 * 2 ^ 59
def prefixEnd_3062617 : Nat := 4983230072969 + 3 ^ 40 * 3062617 * 2
def baseEnd_3062617 : Nat := 1572594581630949230602787

theorem tailTrace_3062617 : CollatzResearch.WordTrace tailWord_3062617 prefixEnd_3062617 1572594581630949230602787 := by
  unfold tailWord_3062617
  simp only [CollatzResearch.WordTrace]
  refine ⟨111702818745669137186306105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74468545830446091457537403 111702818745669137186306105)
  ·
    refine ⟨83777114059251852889729579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111702818745669137186306105 83777114059251852889729579)
    ·
      refine ⟨125665671088877779334594369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83777114059251852889729579 125665671088877779334594369)
      ·
        refine ⟨94249253316658334500945777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125665671088877779334594369 94249253316658334500945777)
        ·
          refine ⟨70686939987493750875709333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94249253316658334500945777 70686939987493750875709333)
          ·
            refine ⟨3313450311913769572298875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70686939987493750875709333 3313450311913769572298875)
            ·
              refine ⟨4970175467870654358448313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313450311913769572298875 4970175467870654358448313)
              ·
                refine ⟨3727631600902990768836235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970175467870654358448313 3727631600902990768836235)
                ·
                  refine ⟨5591447401354486153254353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727631600902990768836235 5591447401354486153254353)
                  ·
                    refine ⟨4193585551015864614940765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591447401354486153254353 4193585551015864614940765)
                    ·
                      refine ⟨1572594581630949230602787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193585551015864614940765 1572594581630949230602787)
                      ·
                        rfl

theorem cell23_3062617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_3062617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062617 prefixEnd_3062617 := by exact prefixLift 3062617
  have htrace : WordTrace (prefixWord ++ tailWord_3062617) baseStart_3062617 baseEnd_3062617 := by
    simpa [prefixWord, tailWord_3062617, baseEnd_3062617] using wordTrace_append hprefix tailTrace_3062617
  have hstable : (prefixWord ++ tailWord_3062617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062617).length < 2 ^ (prefixWord ++ tailWord_3062617).sum := by decide
  have hdescent : baseEnd_3062617 < baseStart_3062617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062653 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3062653 : Nat := 118140960795 + 3062653 * 2 ^ 59
def prefixEnd_3062653 : Nat := 4983230072969 + 3 ^ 40 * 3062653 * 2
def baseEnd_3062653 : Nat := 1572613066934511089752621

theorem tailTrace_3062653 : CollatzResearch.WordTrace tailWord_3062653 prefixEnd_3062653 1572613066934511089752621 := by
  unfold tailWord_3062653
  simp only [CollatzResearch.WordTrace]
  refine ⟨111704131773538715334616613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74469421182359143556411075 111704131773538715334616613)
  ·
    refine ⟨20944524707538509125240615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111704131773538715334616613 20944524707538509125240615)
    ·
      refine ⟨31416787061307763687860923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20944524707538509125240615 31416787061307763687860923)
      ·
        refine ⟨47125180591961645531791385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31416787061307763687860923 47125180591961645531791385)
        ·
          refine ⟨35343885443971234148843539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47125180591961645531791385 35343885443971234148843539)
          ·
            refine ⟨53015828165956851223265309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35343885443971234148843539 53015828165956851223265309)
            ·
              refine ⟨19880935562233819208724491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53015828165956851223265309 19880935562233819208724491)
              ·
                refine ⟨29821403343350728813086737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19880935562233819208724491 29821403343350728813086737)
                ·
                  refine ⟨22366052507513046609815053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29821403343350728813086737 22366052507513046609815053)
                  ·
                    refine ⟨8387269690317392478680645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22366052507513046609815053 8387269690317392478680645)
                    ·
                      refine ⟨1572613066934511089752621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8387269690317392478680645 1572613066934511089752621)
                      ·
                        rfl

theorem cell23_3062653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3062653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062653 prefixEnd_3062653 := by exact prefixLift 3062653
  have htrace : WordTrace (prefixWord ++ tailWord_3062653) baseStart_3062653 baseEnd_3062653 := by
    simpa [prefixWord, tailWord_3062653, baseEnd_3062653] using wordTrace_append hprefix tailTrace_3062653
  have hstable : (prefixWord ++ tailWord_3062653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062653).length < 2 ^ (prefixWord ++ tailWord_3062653).sum := by decide
  have hdescent : baseEnd_3062653 < baseStart_3062653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062654 : List Nat := [4, 2, 3, 1, 3, 1, 1, 8]
def baseStart_3062654 : Nat := 118140960795 + 3062654 * 2 ^ 59
def prefixEnd_3062654 : Nat := 4983230072969 + 3 ^ 40 * 3062654 * 2
def baseEnd_3062654 : Nat := 58244947422783910586671

theorem tailTrace_3062654 : CollatzResearch.WordTrace tailWord_3062654 prefixEnd_3062654 58244947422783910586671 := by
  unfold tailWord_3062654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963021030816886563175377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74469445497690061670268677 13963021030816886563175377)
  ·
    refine ⟨10472265773112664922381533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13963021030816886563175377 10472265773112664922381533)
    ·
      refine ⟨3927099664917249345893075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10472265773112664922381533 3927099664917249345893075)
      ·
        refine ⟨5890649497375874018839613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927099664917249345893075 5890649497375874018839613)
        ·
          refine ⟨2208993561515952757064855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5890649497375874018839613 2208993561515952757064855)
          ·
            refine ⟨3313490342273929135597283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208993561515952757064855 3313490342273929135597283)
            ·
              refine ⟨4970235513410893703395925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313490342273929135597283 4970235513410893703395925)
              ·
                refine ⟨58244947422783910586671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4970235513410893703395925 58244947422783910586671)
                ·
                  rfl

theorem cell23_3062654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_3062654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062654 prefixEnd_3062654 := by exact prefixLift 3062654
  have htrace : WordTrace (prefixWord ++ tailWord_3062654) baseStart_3062654 baseEnd_3062654 := by
    simpa [prefixWord, tailWord_3062654, baseEnd_3062654] using wordTrace_append hprefix tailTrace_3062654
  have hstable : (prefixWord ++ tailWord_3062654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062654).length < 2 ^ (prefixWord ++ tailWord_3062654).sum := by decide
  have hdescent : baseEnd_3062654 < baseStart_3062654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062663 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3062663 : Nat := 118140960795 + 3062663 * 2 ^ 59
def prefixEnd_3062663 : Nat := 4983230072969 + 3 ^ 40 * 3062663 * 2
def baseEnd_3062663 : Nat := 524206067247018683542525

theorem tailTrace_3062663 : CollatzResearch.WordTrace tailWord_3062663 prefixEnd_3062663 524206067247018683542525 := by
  unfold tailWord_3062663
  simp only [CollatzResearch.WordTrace]
  refine ⟨111704496503502487042480643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74469664335668324694987095 111704496503502487042480643)
  ·
    refine ⟨167556744755253730563720965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111704496503502487042480643 167556744755253730563720965)
    ·
      refine ⟨31416889641610074480697681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167556744755253730563720965 31416889641610074480697681)
      ·
        refine ⟨23562667231207555860523261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31416889641610074480697681 23562667231207555860523261)
        ·
          refine ⟨8836000211702833447696223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23562667231207555860523261 8836000211702833447696223)
          ·
            refine ⟨13254000317554250171544335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836000211702833447696223 13254000317554250171544335)
            ·
              refine ⟨19881000476331375257316503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13254000317554250171544335 19881000476331375257316503)
              ·
                refine ⟨29821500714497062885974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19881000476331375257316503 29821500714497062885974755)
                ·
                  refine ⟨44732251071745594328962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29821500714497062885974755 44732251071745594328962133)
                  ·
                    refine ⟨524206067247018683542525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44732251071745594328962133 524206067247018683542525)
                    ·
                      rfl

theorem cell23_3062663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3062663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062663 prefixEnd_3062663 := by exact prefixLift 3062663
  have htrace : WordTrace (prefixWord ++ tailWord_3062663) baseStart_3062663 baseEnd_3062663 := by
    simpa [prefixWord, tailWord_3062663, baseEnd_3062663] using wordTrace_append hprefix tailTrace_3062663
  have hstable : (prefixWord ++ tailWord_3062663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062663).length < 2 ^ (prefixWord ++ tailWord_3062663).sum := by decide
  have hdescent : baseEnd_3062663 < baseStart_3062663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062673 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_3062673 : Nat := 118140960795 + 3062673 * 2 ^ 59
def prefixEnd_3062673 : Nat := 4983230072969 + 3 ^ 40 * 3062673 * 2
def baseEnd_3062673 : Nat := 1572623336547601011502529

theorem tailTrace_3062673 : CollatzResearch.WordTrace tailWord_3062673 prefixEnd_3062673 1572623336547601011502529 := by
  unfold tailWord_3062673
  simp only [CollatzResearch.WordTrace]
  refine ⟨111704861233466258750344673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74469907488977505833563115 111704861233466258750344673)
  ·
    refine ⟨83778645925099694062758505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111704861233466258750344673 83778645925099694062758505)
    ·
      refine ⟨62833984443824770547068879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83778645925099694062758505 62833984443824770547068879)
      ·
        refine ⟨94250976665737155820603319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62833984443824770547068879 94250976665737155820603319)
        ·
          refine ⟨141376464998605733730904979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94250976665737155820603319 141376464998605733730904979)
          ·
            refine ⟨212064697497908600596357469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141376464998605733730904979 212064697497908600596357469)
            ·
              refine ⟨79524261561715725223634051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212064697497908600596357469 79524261561715725223634051)
              ·
                refine ⟨119286392342573587835451077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79524261561715725223634051 119286392342573587835451077)
                ·
                  refine ⟨22366198564232547719147077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119286392342573587835451077 22366198564232547719147077)
                  ·
                    refine ⟨4193662230793602697340077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22366198564232547719147077 4193662230793602697340077)
                    ·
                      refine ⟨1572623336547601011502529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193662230793602697340077 1572623336547601011502529)
                      ·
                        rfl

theorem cell23_3062673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_3062673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062673 prefixEnd_3062673 := by exact prefixLift 3062673
  have htrace : WordTrace (prefixWord ++ tailWord_3062673) baseStart_3062673 baseEnd_3062673 := by
    simpa [prefixWord, tailWord_3062673, baseEnd_3062673] using wordTrace_append hprefix tailTrace_3062673
  have hstable : (prefixWord ++ tailWord_3062673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062673).length < 2 ^ (prefixWord ++ tailWord_3062673).sum := by decide
  have hdescent : baseEnd_3062673 < baseStart_3062673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062687 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3062687 : Nat := 118140960795 + 3062687 * 2 ^ 59
def prefixEnd_3062687 : Nat := 4983230072969 + 3 ^ 40 * 3062687 * 2
def baseEnd_3062687 : Nat := 1572630525276763956727465

theorem tailTrace_3062687 : CollatzResearch.WordTrace tailWord_3062687 prefixEnd_3062687 1572630525276763956727465 := by
  unfold tailWord_3062687
  simp only [CollatzResearch.WordTrace]
  refine ⟨111705371855415539141354315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74470247903610359427569543 111705371855415539141354315)
  ·
    refine ⟨167558057783123308712031473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111705371855415539141354315 167558057783123308712031473)
    ·
      refine ⟨125668543337342481534023605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167558057783123308712031473 125668543337342481534023605)
      ·
        refine ⟨11781425937875857643814713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125668543337342481534023605 11781425937875857643814713)
        ·
          refine ⟨8836069453406893232861035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11781425937875857643814713 8836069453406893232861035)
          ·
            refine ⟨13254104180110339849291553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836069453406893232861035 13254104180110339849291553)
            ·
              refine ⟨9940578135082754886968665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254104180110339849291553 9940578135082754886968665)
              ·
                refine ⟨7455433601312066165226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9940578135082754886968665 7455433601312066165226499)
                ·
                  refine ⟨11183150401968099247839749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455433601312066165226499 11183150401968099247839749)
                  ·
                    refine ⟨2096840700369018608969953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11183150401968099247839749 2096840700369018608969953)
                    ·
                      refine ⟨1572630525276763956727465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096840700369018608969953 1572630525276763956727465)
                      ·
                        rfl

theorem cell23_3062687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3062687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062687 prefixEnd_3062687 := by exact prefixLift 3062687
  have htrace : WordTrace (prefixWord ++ tailWord_3062687) baseStart_3062687 baseEnd_3062687 := by
    simpa [prefixWord, tailWord_3062687, baseEnd_3062687] using wordTrace_append hprefix tailTrace_3062687
  have hstable : (prefixWord ++ tailWord_3062687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062687).length < 2 ^ (prefixWord ++ tailWord_3062687).sum := by decide
  have hdescent : baseEnd_3062687 < baseStart_3062687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062720 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_3062720 : Nat := 118140960795 + 3062720 * 2 ^ 59
def prefixEnd_3062720 : Nat := 4983230072969 + 3 ^ 40 * 3062720 * 2
def baseEnd_3062720 : Nat := 1572647470138362327614813

theorem tailTrace_3062720 : CollatzResearch.WordTrace tailWord_3062720 prefixEnd_3062720 1572647470138362327614813 := by
  unfold tailWord_3062720
  simp only [CollatzResearch.WordTrace]
  refine ⟨55853287732147992888652807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74471050309530657184870409 55853287732147992888652807)
  ·
    refine ⟨83779931598221989332979211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55853287732147992888652807 83779931598221989332979211)
    ·
      refine ⟨125669897397332983999468817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83779931598221989332979211 125669897397332983999468817)
      ·
        refine ⟨94252423047999737999601613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125669897397332983999468817 94252423047999737999601613)
        ·
          refine ⟨35344658642999901749850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94252423047999737999601613 35344658642999901749850605)
          ·
            refine ⟨13254246991124963156193977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35344658642999901749850605 13254246991124963156193977)
            ·
              refine ⟨9940685243343722367145483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254246991124963156193977 9940685243343722367145483)
              ·
                refine ⟨14911027865015583550718225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9940685243343722367145483 14911027865015583550718225)
                ·
                  refine ⟨11183270898761687663038669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14911027865015583550718225 11183270898761687663038669)
                  ·
                    refine ⟨4193726587035632873639501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11183270898761687663038669 4193726587035632873639501)
                    ·
                      refine ⟨1572647470138362327614813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193726587035632873639501 1572647470138362327614813)
                      ·
                        rfl

theorem cell23_3062720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_3062720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062720 prefixEnd_3062720 := by exact prefixLift 3062720
  have htrace : WordTrace (prefixWord ++ tailWord_3062720) baseStart_3062720 baseEnd_3062720 := by
    simpa [prefixWord, tailWord_3062720, baseEnd_3062720] using wordTrace_append hprefix tailTrace_3062720
  have hstable : (prefixWord ++ tailWord_3062720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062720).length < 2 ^ (prefixWord ++ tailWord_3062720).sum := by decide
  have hdescent : baseEnd_3062720 < baseStart_3062720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062723 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 4, 5]
def baseStart_3062723 : Nat := 118140960795 + 3062723 * 2 ^ 59
def prefixEnd_3062723 : Nat := 4983230072969 + 3 ^ 40 * 3062723 * 2
def baseEnd_3062723 : Nat := 524216336860108605292433

theorem tailTrace_3062723 : CollatzResearch.WordTrace tailWord_3062723 prefixEnd_3062723 524216336860108605292433 := by
  unfold tailWord_3062723
  simp only [CollatzResearch.WordTrace]
  refine ⟨111706684883285117289664823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74471123255523411526443215 111706684883285117289664823)
  ·
    refine ⟨167560027324927675934497235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111706684883285117289664823 167560027324927675934497235)
    ·
      refine ⟨251340040987391513901745853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167560027324927675934497235 251340040987391513901745853)
      ·
        refine ⟨94252515370271817713154695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251340040987391513901745853 94252515370271817713154695)
        ·
          refine ⟨141378773055407726569732043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94252515370271817713154695 141378773055407726569732043)
          ·
            refine ⟨212068159583111589854598065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141378773055407726569732043 212068159583111589854598065)
            ·
              refine ⟨159051119687333692390948549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212068159583111589854598065 159051119687333692390948549)
              ·
                refine ⟨29822084941375067323302853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159051119687333692390948549 29822084941375067323302853)
                ·
                  refine ⟨5591640926507825123119285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29822084941375067323302853 5591640926507825123119285)
                  ·
                    refine ⟨524216336860108605292433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591640926507825123119285 524216336860108605292433)
                    ·
                      rfl

theorem cell23_3062723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].length) (baseStart_3062723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062723 prefixEnd_3062723 := by exact prefixLift 3062723
  have htrace : WordTrace (prefixWord ++ tailWord_3062723) baseStart_3062723 baseEnd_3062723 := by
    simpa [prefixWord, tailWord_3062723, baseEnd_3062723] using wordTrace_append hprefix tailTrace_3062723
  have hstable : (prefixWord ++ tailWord_3062723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062723).length < 2 ^ (prefixWord ++ tailWord_3062723).sum := by decide
  have hdescent : baseEnd_3062723 < baseStart_3062723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062740 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3062740 : Nat := 118140960795 + 3062740 * 2 ^ 59
def prefixEnd_3062740 : Nat := 4983230072969 + 3 ^ 40 * 3062740 * 2
def baseEnd_3062740 : Nat := 524219246583817416454907

theorem tailTrace_3062740 : CollatzResearch.WordTrace tailWord_3062740 prefixEnd_3062740 524219246583817416454907 := by
  unfold tailWord_3062740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55853652462111764596516837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74471536616149019462022449 55853652462111764596516837)
  ·
    refine ⟨10472559836645955861846907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55853652462111764596516837 10472559836645955861846907)
    ·
      refine ⟨15708839754968933792770361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10472559836645955861846907 15708839754968933792770361)
      ·
        refine ⟨11781629816226700344577771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15708839754968933792770361 11781629816226700344577771)
        ·
          refine ⟨17672444724340050516866657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11781629816226700344577771 17672444724340050516866657)
          ·
            refine ⟨13254333543255037887649993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17672444724340050516866657 13254333543255037887649993)
            ·
              refine ⟨9940750157441278415737495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254333543255037887649993 9940750157441278415737495)
              ·
                refine ⟨14911125236161917623606243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9940750157441278415737495 14911125236161917623606243)
                ·
                  refine ⟨22366687854242876435409365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14911125236161917623606243 22366687854242876435409365)
                  ·
                    refine ⟨524219246583817416454907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22366687854242876435409365 524219246583817416454907)
                    ·
                      rfl

theorem cell23_3062740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3062740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062740 prefixEnd_3062740 := by exact prefixLift 3062740
  have htrace : WordTrace (prefixWord ++ tailWord_3062740) baseStart_3062740 baseEnd_3062740 := by
    simpa [prefixWord, tailWord_3062740, baseEnd_3062740] using wordTrace_append hprefix tailTrace_3062740
  have hstable : (prefixWord ++ tailWord_3062740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062740).length < 2 ^ (prefixWord ++ tailWord_3062740).sum := by decide
  have hdescent : baseEnd_3062740 < baseStart_3062740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062760 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3062760 : Nat := 118140960795 + 3062760 * 2 ^ 59
def prefixEnd_3062760 : Nat := 4983230072969 + 3 ^ 40 * 3062760 * 2
def baseEnd_3062760 : Nat := 1572668009364542171114629

theorem tailTrace_3062760 : CollatzResearch.WordTrace tailWord_3062760 prefixEnd_3062760 1572668009364542171114629 := by
  unfold tailWord_3062760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55854017192075536304380867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74472022922767381739174489 55854017192075536304380867)
  ·
    refine ⟨83781025788113304456571301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55854017192075536304380867 83781025788113304456571301)
    ·
      refine ⟨15708942335271244585607119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83781025788113304456571301 15708942335271244585607119)
      ·
        refine ⟨23563413502906866878410679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15708942335271244585607119 23563413502906866878410679)
        ·
          refine ⟨35345120254360300317616019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23563413502906866878410679 35345120254360300317616019)
          ·
            refine ⟨53017680381540450476424029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35345120254360300317616019 53017680381540450476424029)
            ·
              refine ⟨19881630143077668928659011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53017680381540450476424029 19881630143077668928659011)
              ·
                refine ⟨29822445214616503392988517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19881630143077668928659011 29822445214616503392988517)
                ·
                  refine ⟨5591708477740594386185347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29822445214616503392988517 5591708477740594386185347)
                  ·
                    refine ⟨8387562716610891579278021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591708477740594386185347 8387562716610891579278021)
                    ·
                      refine ⟨1572668009364542171114629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8387562716610891579278021 1572668009364542171114629)
                      ·
                        rfl

theorem cell23_3062760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3062760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062760 prefixEnd_3062760 := by exact prefixLift 3062760
  have htrace : WordTrace (prefixWord ++ tailWord_3062760) baseStart_3062760 baseEnd_3062760 := by
    simpa [prefixWord, tailWord_3062760, baseEnd_3062760] using wordTrace_append hprefix tailTrace_3062760
  have hstable : (prefixWord ++ tailWord_3062760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062760).length < 2 ^ (prefixWord ++ tailWord_3062760).sum := by decide
  have hdescent : baseEnd_3062760 < baseStart_3062760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062772 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3062772 : Nat := 118140960795 + 3062772 * 2 ^ 59
def prefixEnd_3062772 : Nat := 4983230072969 + 3 ^ 40 * 3062772 * 2
def baseEnd_3062772 : Nat := 1572674171132396124164575

theorem tailTrace_3062772 : CollatzResearch.WordTrace tailWord_3062772 prefixEnd_3062772 1572674171132396124164575 := by
  unfold tailWord_3062772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55854236030053799329099285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74472314706738399105465713 55854236030053799329099285)
  ·
    refine ⟨2618167313908771843551529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55854236030053799329099285 2618167313908771843551529)
    ·
      refine ⟨1963625485431578882663647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2618167313908771843551529 1963625485431578882663647)
      ·
        refine ⟨2945438228147368323995471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963625485431578882663647 2945438228147368323995471)
        ·
          refine ⟨4418157342221052485993207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945438228147368323995471 4418157342221052485993207)
          ·
            refine ⟨6627236013331578728989811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418157342221052485993207 6627236013331578728989811)
            ·
              refine ⟨9940854019997368093484717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627236013331578728989811 9940854019997368093484717)
              ·
                refine ⟨3727820257499013035056769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940854019997368093484717 3727820257499013035056769)
                ·
                  refine ⟨2795865193124259776292577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3727820257499013035056769 2795865193124259776292577)
                  ·
                    refine ⟨2096898894843194832219433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795865193124259776292577 2096898894843194832219433)
                    ·
                      refine ⟨1572674171132396124164575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096898894843194832219433 1572674171132396124164575)
                      ·
                        rfl

theorem cell23_3062772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3062772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062772 prefixEnd_3062772 := by exact prefixLift 3062772
  have htrace : WordTrace (prefixWord ++ tailWord_3062772) baseStart_3062772 baseEnd_3062772 := by
    simpa [prefixWord, tailWord_3062772, baseEnd_3062772] using wordTrace_append hprefix tailTrace_3062772
  have hstable : (prefixWord ++ tailWord_3062772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062772).length < 2 ^ (prefixWord ++ tailWord_3062772).sum := by decide
  have hdescent : baseEnd_3062772 < baseStart_3062772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062803 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_3062803 : Nat := 118140960795 + 3062803 * 2 ^ 59
def prefixEnd_3062803 : Nat := 4983230072969 + 3 ^ 40 * 3062803 * 2
def baseEnd_3062803 : Nat := 1572690089032685502876931

theorem tailTrace_3062803 : CollatzResearch.WordTrace tailWord_3062803 prefixEnd_3062803 1572690089032685502876931 := by
  unfold tailWord_3062803
  simp only [CollatzResearch.WordTrace]
  refine ⟨111709602722995290952577063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74473068481996860635051375 111709602722995290952577063)
  ·
    refine ⟨167564404084492936428865595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111709602722995290952577063 167564404084492936428865595)
    ·
      refine ⟨251346606126739404643298393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167564404084492936428865595 251346606126739404643298393)
      ·
        refine ⟨188509954595054553482473795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251346606126739404643298393 188509954595054553482473795)
        ·
          refine ⟨282764931892581830223710693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188509954595054553482473795 282764931892581830223710693)
          ·
            refine ⟨53018424729859093166945755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282764931892581830223710693 53018424729859093166945755)
            ·
              refine ⟨79527637094788639750418633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53018424729859093166945755 79527637094788639750418633)
              ·
                refine ⟨59645727821091479812813975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79527637094788639750418633 59645727821091479812813975)
                ·
                  refine ⟨89468591731637219719220963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59645727821091479812813975 89468591731637219719220963)
                  ·
                    refine ⟨134202887597455829578831445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89468591731637219719220963 134202887597455829578831445)
                    ·
                      refine ⟨1572690089032685502876931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 134202887597455829578831445 1572690089032685502876931)
                      ·
                        rfl

theorem cell23_3062803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_3062803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062803 prefixEnd_3062803 := by exact prefixLift 3062803
  have htrace : WordTrace (prefixWord ++ tailWord_3062803) baseStart_3062803 baseEnd_3062803 := by
    simpa [prefixWord, tailWord_3062803, baseEnd_3062803] using wordTrace_append hprefix tailTrace_3062803
  have hstable : (prefixWord ++ tailWord_3062803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062803).length < 2 ^ (prefixWord ++ tailWord_3062803).sum := by decide
  have hdescent : baseEnd_3062803 < baseStart_3062803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062817 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 6]
def baseStart_3062817 : Nat := 118140960795 + 3062817 * 2 ^ 59
def prefixEnd_3062817 : Nat := 4983230072969 + 3 ^ 40 * 3062817 * 2
def baseEnd_3062817 : Nat := 174744141973538716455763

theorem tailTrace_3062817 : CollatzResearch.WordTrace tailWord_3062817 prefixEnd_3062817 174744141973538716455763 := by
  unfold tailWord_3062817
  simp only [CollatzResearch.WordTrace]
  refine ⟨111710113344944571343586705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74473408896629714229057803 111710113344944571343586705)
  ·
    refine ⟨83782585008708428507690029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111710113344944571343586705 83782585008708428507690029)
    ·
      refine ⟨31418469378265660690383761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83782585008708428507690029 31418469378265660690383761)
      ·
        refine ⟨23563852033699245517787821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31418469378265660690383761 23563852033699245517787821)
        ·
          refine ⟨8836444512637217069170433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23563852033699245517787821 8836444512637217069170433)
          ·
            refine ⟨6627333384477912801877825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836444512637217069170433 6627333384477912801877825)
            ·
              refine ⟨4970500038358434601408369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627333384477912801877825 4970500038358434601408369)
              ·
                refine ⟨3727875028768825951056277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970500038358434601408369 3727875028768825951056277)
                ·
                  refine ⟨174744141973538716455763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3727875028768825951056277 174744141973538716455763)
                  ·
                    rfl

theorem cell23_3062817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_3062817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062817 prefixEnd_3062817 := by exact prefixLift 3062817
  have htrace : WordTrace (prefixWord ++ tailWord_3062817) baseStart_3062817 baseEnd_3062817 := by
    simpa [prefixWord, tailWord_3062817, baseEnd_3062817] using wordTrace_append hprefix tailTrace_3062817
  have hstable : (prefixWord ++ tailWord_3062817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062817).length < 2 ^ (prefixWord ++ tailWord_3062817).sum := by decide
  have hdescent : baseEnd_3062817 < baseStart_3062817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062827 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 3]
def baseStart_3062827 : Nat := 118140960795 + 3062827 * 2 ^ 59
def prefixEnd_3062827 : Nat := 4983230072969 + 3 ^ 40 * 3062827 * 2
def baseEnd_3062827 : Nat := 1572702412568393408976821

theorem tailTrace_3062827 : CollatzResearch.WordTrace tailWord_3062827 prefixEnd_3062827 1572702412568393408976821 := by
  unfold tailWord_3062827
  simp only [CollatzResearch.WordTrace]
  refine ⟨111710478074908343051450735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74473652049938895367633823 111710478074908343051450735)
  ·
    refine ⟨167565717112362514577176103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111710478074908343051450735 167565717112362514577176103)
    ·
      refine ⟨251348575668543771865764155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167565717112362514577176103 251348575668543771865764155)
      ·
        refine ⟨377022863502815657798646233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251348575668543771865764155 377022863502815657798646233)
        ·
          refine ⟨282767147627111743348984675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377022863502815657798646233 282767147627111743348984675)
          ·
            refine ⟨424150721440667615023477013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282767147627111743348984675 424150721440667615023477013)
            ·
              refine ⟨19882065067531294454225485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 424150721440667615023477013 19882065067531294454225485)
              ·
                refine ⟨7455774400324235420334557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19882065067531294454225485 7455774400324235420334557)
                ·
                  refine ⟨2795915400121588282625459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7455774400324235420334557 2795915400121588282625459)
                  ·
                    refine ⟨4193873100182382423938189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2795915400121588282625459 4193873100182382423938189)
                    ·
                      refine ⟨1572702412568393408976821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193873100182382423938189 1572702412568393408976821)
                      ·
                        rfl

theorem cell23_3062827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 3].length) (baseStart_3062827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062827 prefixEnd_3062827 := by exact prefixLift 3062827
  have htrace : WordTrace (prefixWord ++ tailWord_3062827) baseStart_3062827 baseEnd_3062827 := by
    simpa [prefixWord, tailWord_3062827, baseEnd_3062827] using wordTrace_append hprefix tailTrace_3062827
  have hstable : (prefixWord ++ tailWord_3062827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062827).length < 2 ^ (prefixWord ++ tailWord_3062827).sum := by decide
  have hdescent : baseEnd_3062827 < baseStart_3062827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062837 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_3062837 : Nat := 118140960795 + 3062837 * 2 ^ 59
def prefixEnd_3062837 : Nat := 4983230072969 + 3 ^ 40 * 3062837 * 2
def baseEnd_3062837 : Nat := 1572707547374938369851775

theorem tailTrace_3062837 : CollatzResearch.WordTrace tailWord_3062837 prefixEnd_3062837 1572707547374938369851775 := by
  unfold tailWord_3062837
  simp only [CollatzResearch.WordTrace]
  refine ⟨111710842804872114759314765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74473895203248076506209843 111710842804872114759314765)
  ·
    refine ⟨41891566051827043034743037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111710842804872114759314765 41891566051827043034743037)
    ·
      refine ⟨15709337269435141138028639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41891566051827043034743037 15709337269435141138028639)
      ·
        refine ⟨23564005904152711707042959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709337269435141138028639 23564005904152711707042959)
        ·
          refine ⟨35346008856229067560564439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23564005904152711707042959 35346008856229067560564439)
          ·
            refine ⟨53019013284343601340846659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35346008856229067560564439 53019013284343601340846659)
            ·
              refine ⟨79528519926515402011269989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53019013284343601340846659 79528519926515402011269989)
              ·
                refine ⟨14911597486221637877113123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79528519926515402011269989 14911597486221637877113123)
                ·
                  refine ⟨22367396229332456815669685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14911597486221637877113123 22367396229332456815669685)
                  ·
                    refine ⟨2096943396499917826469033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22367396229332456815669685 2096943396499917826469033)
                    ·
                      refine ⟨1572707547374938369851775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2096943396499917826469033 1572707547374938369851775)
                      ·
                        rfl

theorem cell23_3062837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_3062837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062837 prefixEnd_3062837 := by exact prefixLift 3062837
  have htrace : WordTrace (prefixWord ++ tailWord_3062837) baseStart_3062837 baseEnd_3062837 := by
    simpa [prefixWord, tailWord_3062837, baseEnd_3062837] using wordTrace_append hprefix tailTrace_3062837
  have hstable : (prefixWord ++ tailWord_3062837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062837).length < 2 ^ (prefixWord ++ tailWord_3062837).sum := by decide
  have hdescent : baseEnd_3062837 < baseStart_3062837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062844 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_3062844 : Nat := 118140960795 + 3062844 * 2 ^ 59
def prefixEnd_3062844 : Nat := 4983230072969 + 3 ^ 40 * 3062844 * 2
def baseEnd_3062844 : Nat := 1572711141739519842464243

theorem tailTrace_3062844 : CollatzResearch.WordTrace tailWord_3062844 prefixEnd_3062844 1572711141739519842464243 := by
  unfold tailWord_3062844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55855549057923377477409793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74474065410564503303213057 55855549057923377477409793)
  ·
    refine ⟨41891661793442533108057345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55855549057923377477409793 41891661793442533108057345)
    ·
      refine ⟨31418746345081899831043009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41891661793442533108057345 31418746345081899831043009)
      ·
        refine ⟨23564059758811424873282257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31418746345081899831043009 23564059758811424873282257)
        ·
          refine ⟨17673044819108568654961693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23564059758811424873282257 17673044819108568654961693)
          ·
            refine ⟨6627391807165713245610635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17673044819108568654961693 6627391807165713245610635)
            ·
              refine ⟨9941087710748569868415953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627391807165713245610635 9941087710748569868415953)
              ·
                refine ⟨7455815783061427401311965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941087710748569868415953 7455815783061427401311965)
                ·
                  refine ⟨2795930918648035275491987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7455815783061427401311965 2795930918648035275491987)
                  ·
                    refine ⟨4193896377972052913237981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2795930918648035275491987 4193896377972052913237981)
                    ·
                      refine ⟨1572711141739519842464243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193896377972052913237981 1572711141739519842464243)
                      ·
                        rfl

theorem cell23_3062844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_3062844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062844 prefixEnd_3062844 := by exact prefixLift 3062844
  have htrace : WordTrace (prefixWord ++ tailWord_3062844) baseStart_3062844 baseEnd_3062844 := by
    simpa [prefixWord, tailWord_3062844, baseEnd_3062844] using wordTrace_append hprefix tailTrace_3062844
  have hstable : (prefixWord ++ tailWord_3062844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062844).length < 2 ^ (prefixWord ++ tailWord_3062844).sum := by decide
  have hdescent : baseEnd_3062844 < baseStart_3062844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062878 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3062878 : Nat := 118140960795 + 3062878 * 2 ^ 59
def prefixEnd_3062878 : Nat := 4983230072969 + 3 ^ 40 * 3062878 * 2
def baseEnd_3062878 : Nat := 1572728600081772709439087

theorem tailTrace_3062878 : CollatzResearch.WordTrace tailWord_3062878 prefixEnd_3062878 1572728600081772709439087 := by
  unfold tailWord_3062878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964042274715447345194661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74474892131815719174371525 13964042274715447345194661)
  ·
    refine ⟨2618257926509146377223999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13964042274715447345194661 2618257926509146377223999)
    ·
      refine ⟨3927386889763719565835999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2618257926509146377223999 3927386889763719565835999)
      ·
        refine ⟨5891080334645579348753999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927386889763719565835999 5891080334645579348753999)
        ·
          refine ⟨8836620501968369023130999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891080334645579348753999 8836620501968369023130999)
          ·
            refine ⟨13254930752952553534696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836620501968369023130999 13254930752952553534696499)
            ·
              refine ⟨19882396129428830302044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13254930752952553534696499 19882396129428830302044749)
              ·
                refine ⟨7455898548535811363266781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19882396129428830302044749 7455898548535811363266781)
                ·
                  refine ⟨2795961955700929261225043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7455898548535811363266781 2795961955700929261225043)
                  ·
                    refine ⟨4193942933551393891837565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2795961955700929261225043 4193942933551393891837565)
                    ·
                      refine ⟨1572728600081772709439087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4193942933551393891837565 1572728600081772709439087)
                      ·
                        rfl

theorem cell23_3062878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3062878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062878 prefixEnd_3062878 := by exact prefixLift 3062878
  have htrace : WordTrace (prefixWord ++ tailWord_3062878) baseStart_3062878 baseEnd_3062878 := by
    simpa [prefixWord, tailWord_3062878, baseEnd_3062878] using wordTrace_append hprefix tailTrace_3062878
  have hstable : (prefixWord ++ tailWord_3062878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062878).length < 2 ^ (prefixWord ++ tailWord_3062878).sum := by decide
  have hdescent : baseEnd_3062878 < baseStart_3062878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062880 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3062880 : Nat := 118140960795 + 3062880 * 2 ^ 59
def prefixEnd_3062880 : Nat := 4983230072969 + 3 ^ 40 * 3062880 * 2
def baseEnd_3062880 : Nat := 1572729627043081701614077

theorem tailTrace_3062880 : CollatzResearch.WordTrace tailWord_3062880 prefixEnd_3062880 1572729627043081701614077 := by
  unfold tailWord_3062880
  simp only [CollatzResearch.WordTrace]
  refine ⟨55856205571858166551565047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74474940762477555402086729 55856205571858166551565047)
  ·
    refine ⟨83784308357787249827347571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55856205571858166551565047 83784308357787249827347571)
    ·
      refine ⟨125676462536680874741021357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83784308357787249827347571 125676462536680874741021357)
      ·
        refine ⟨47128673451255328027883009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125676462536680874741021357 47128673451255328027883009)
        ·
          refine ⟨35346505088441496020912257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47128673451255328027883009 35346505088441496020912257)
          ·
            refine ⟨26509878816331122015684193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35346505088441496020912257 26509878816331122015684193)
            ·
              refine ⟨19882409112248341511763145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26509878816331122015684193 19882409112248341511763145)
              ·
                refine ⟨14911806834186256133822359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19882409112248341511763145 14911806834186256133822359)
                ·
                  refine ⟨22367710251279384200733539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14911806834186256133822359 22367710251279384200733539)
                  ·
                    refine ⟨33551565376919076301100309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22367710251279384200733539 33551565376919076301100309)
                    ·
                      refine ⟨1572729627043081701614077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33551565376919076301100309 1572729627043081701614077)
                      ·
                        rfl

theorem cell23_3062880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3062880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062880 prefixEnd_3062880 := by exact prefixLift 3062880
  have htrace : WordTrace (prefixWord ++ tailWord_3062880) baseStart_3062880 baseEnd_3062880 := by
    simpa [prefixWord, tailWord_3062880, baseEnd_3062880] using wordTrace_append hprefix tailTrace_3062880
  have hstable : (prefixWord ++ tailWord_3062880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062880).length < 2 ^ (prefixWord ++ tailWord_3062880).sum := by decide
  have hdescent : baseEnd_3062880 < baseStart_3062880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062887 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3062887 : Nat := 118140960795 + 3062887 * 2 ^ 59
def prefixEnd_3062887 : Nat := 4983230072969 + 3 ^ 40 * 3062887 * 2
def baseEnd_3062887 : Nat := 1572733221407663174226545

theorem tailTrace_3062887 : CollatzResearch.WordTrace tailWord_3062887 prefixEnd_3062887 1572733221407663174226545 := by
  unfold tailWord_3062887
  simp only [CollatzResearch.WordTrace]
  refine ⟨111712666454690973298634915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74475110969793982199089943 111712666454690973298634915)
  ·
    refine ⟨167568999682036459947952373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111712666454690973298634915 167568999682036459947952373)
    ·
      refine ⟨15709593720190918120120535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167568999682036459947952373 15709593720190918120120535)
      ·
        refine ⟨23564390580286377180180803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709593720190918120120535 23564390580286377180180803)
        ·
          refine ⟨35346585870429565770271205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23564390580286377180180803 35346585870429565770271205)
          ·
            refine ⟨6627484850705543581925851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35346585870429565770271205 6627484850705543581925851)
            ·
              refine ⟨9941227276058315372888777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627484850705543581925851 9941227276058315372888777)
              ·
                refine ⟨7455920457043736529666583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941227276058315372888777 7455920457043736529666583)
                ·
                  refine ⟨11183880685565604794499875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455920457043736529666583 11183880685565604794499875)
                  ·
                    refine ⟨16775821028348407191749813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11183880685565604794499875 16775821028348407191749813)
                    ·
                      refine ⟨1572733221407663174226545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16775821028348407191749813 1572733221407663174226545)
                      ·
                        rfl

theorem cell23_3062887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3062887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062887 prefixEnd_3062887 := by exact prefixLift 3062887
  have htrace : WordTrace (prefixWord ++ tailWord_3062887) baseStart_3062887 baseEnd_3062887 := by
    simpa [prefixWord, tailWord_3062887, baseEnd_3062887] using wordTrace_append hprefix tailTrace_3062887
  have hstable : (prefixWord ++ tailWord_3062887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062887).length < 2 ^ (prefixWord ++ tailWord_3062887).sum := by decide
  have hdescent : baseEnd_3062887 < baseStart_3062887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062894 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3062894 : Nat := 118140960795 + 3062894 * 2 ^ 59
def prefixEnd_3062894 : Nat := 4983230072969 + 3 ^ 40 * 3062894 * 2
def baseEnd_3062894 : Nat := 524245605257414882279671

theorem tailTrace_3062894 : CollatzResearch.WordTrace tailWord_3062894 prefixEnd_3062894 524245605257414882279671 := by
  unfold tailWord_3062894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964115220708201686767467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74475281177110408996093157 13964115220708201686767467)
  ·
    refine ⟨20946172831062302530151201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964115220708201686767467 20946172831062302530151201)
    ·
      refine ⟨15709629623296726897613401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20946172831062302530151201 15709629623296726897613401)
      ·
        refine ⟨11782222217472545173210051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15709629623296726897613401 11782222217472545173210051)
        ·
          refine ⟨17673333326208817759815077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11782222217472545173210051 17673333326208817759815077)
          ·
            refine ⟨3313749998664153329965327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17673333326208817759815077 3313749998664153329965327)
            ·
              refine ⟨4970624997996229994947991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313749998664153329965327 4970624997996229994947991)
              ·
                refine ⟨7455937496994344992421987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970624997996229994947991 7455937496994344992421987)
                ·
                  refine ⟨11183906245491517488632981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455937496994344992421987 11183906245491517488632981)
                  ·
                    refine ⟨524245605257414882279671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11183906245491517488632981 524245605257414882279671)
                    ·
                      rfl

theorem cell23_3062894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3062894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062894 prefixEnd_3062894 := by exact prefixLift 3062894
  have htrace : WordTrace (prefixWord ++ tailWord_3062894) baseStart_3062894 baseEnd_3062894 := by
    simpa [prefixWord, tailWord_3062894, baseEnd_3062894] using wordTrace_append hprefix tailTrace_3062894
  have hstable : (prefixWord ++ tailWord_3062894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062894).length < 2 ^ (prefixWord ++ tailWord_3062894).sum := by decide
  have hdescent : baseEnd_3062894 < baseStart_3062894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062935 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_3062935 : Nat := 118140960795 + 3062935 * 2 ^ 59
def prefixEnd_3062935 : Nat := 4983230072969 + 3 ^ 40 * 3062935 * 2
def baseEnd_3062935 : Nat := 1572757868479078986426325

theorem tailTrace_3062935 : CollatzResearch.WordTrace tailWord_3062935 prefixEnd_3062935 1572757868479078986426325 := by
  unfold tailWord_3062935
  simp only [CollatzResearch.WordTrace]
  refine ⟨111714417158517077496382259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74476278105678051664254839 111714417158517077496382259)
  ·
    refine ⟨167571625737775616244573389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111714417158517077496382259 167571625737775616244573389)
    ·
      refine ⟨62839359651665856091715021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167571625737775616244573389 62839359651665856091715021)
      ·
        refine ⟨23564759869374696034393133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62839359651665856091715021 23564759869374696034393133)
        ·
          refine ⟨8836784951015511012897425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23564759869374696034393133 8836784951015511012897425)
          ·
            refine ⟨6627588713261633259673069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836784951015511012897425 6627588713261633259673069)
            ·
              refine ⟨2485345767473112472377401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6627588713261633259673069 2485345767473112472377401)
              ·
                refine ⟨1864009325604834354283051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485345767473112472377401 1864009325604834354283051)
                ·
                  refine ⟨2796013988407251531424577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864009325604834354283051 2796013988407251531424577)
                  ·
                    refine ⟨2097010491305438648568433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2796013988407251531424577 2097010491305438648568433)
                    ·
                      refine ⟨1572757868479078986426325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097010491305438648568433 1572757868479078986426325)
                      ·
                        rfl

theorem cell23_3062935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_3062935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062935 prefixEnd_3062935 := by exact prefixLift 3062935
  have htrace : WordTrace (prefixWord ++ tailWord_3062935) baseStart_3062935 baseEnd_3062935 := by
    simpa [prefixWord, tailWord_3062935, baseEnd_3062935] using wordTrace_append hprefix tailTrace_3062935
  have hstable : (prefixWord ++ tailWord_3062935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062935).length < 2 ^ (prefixWord ++ tailWord_3062935).sum := by decide
  have hdescent : baseEnd_3062935 < baseStart_3062935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062944 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2]
def baseStart_3062944 : Nat := 118140960795 + 3062944 * 2 ^ 59
def prefixEnd_3062944 : Nat := 4983230072969 + 3 ^ 40 * 3062944 * 2
def baseEnd_3062944 : Nat := 1572762489804969451213783

theorem tailTrace_3062944 : CollatzResearch.WordTrace tailWord_3062944 prefixEnd_3062944 1572762489804969451213783 := by
  unfold tailWord_3062944
  simp only [CollatzResearch.WordTrace]
  refine ⟨55857372707742236016729943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74476496943656314688973257 55857372707742236016729943)
  ·
    refine ⟨83786059061613354025094915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55857372707742236016729943 83786059061613354025094915)
    ·
      refine ⟨125679088592420031037642373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83786059061613354025094915 125679088592420031037642373)
      ·
        refine ⟨23564829111078755819557945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125679088592420031037642373 23564829111078755819557945)
        ·
          refine ⟨17673621833309066864668459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23564829111078755819557945 17673621833309066864668459)
          ·
            refine ⟨26510432749963600297002689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17673621833309066864668459 26510432749963600297002689)
            ·
              refine ⟨19882824562472700222752017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26510432749963600297002689 19882824562472700222752017)
              ·
                refine ⟨14912118421854525167064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19882824562472700222752017 14912118421854525167064013)
                ·
                  refine ⟨5592044408195446937649005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14912118421854525167064013 5592044408195446937649005)
                  ·
                    refine ⟨2097016653073292601618377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5592044408195446937649005 2097016653073292601618377)
                    ·
                      refine ⟨1572762489804969451213783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097016653073292601618377 1572762489804969451213783)
                      ·
                        rfl

theorem cell23_3062944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_3062944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062944 prefixEnd_3062944 := by exact prefixLift 3062944
  have htrace : WordTrace (prefixWord ++ tailWord_3062944) baseStart_3062944 baseEnd_3062944 := by
    simpa [prefixWord, tailWord_3062944, baseEnd_3062944] using wordTrace_append hprefix tailTrace_3062944
  have hstable : (prefixWord ++ tailWord_3062944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062944).length < 2 ^ (prefixWord ++ tailWord_3062944).sum := by decide
  have hdescent : baseEnd_3062944 < baseStart_3062944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062960 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3062960 : Nat := 118140960795 + 3062960 * 2 ^ 59
def prefixEnd_3062960 : Nat := 4983230072969 + 3 ^ 40 * 3062960 * 2
def baseEnd_3062960 : Nat := 1572770705495441388613709

theorem tailTrace_3062960 : CollatzResearch.WordTrace tailWord_3062960 prefixEnd_3062960 1572770705495441388613709 := by
  unfold tailWord_3062960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55857664491713253383021167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74476885988951004510694889 55857664491713253383021167)
  ·
    refine ⟨83786496737569880074531751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55857664491713253383021167 83786496737569880074531751)
    ·
      refine ⟨125679745106354820111797627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83786496737569880074531751 125679745106354820111797627)
      ·
        refine ⟨188519617659532230167696441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125679745106354820111797627 188519617659532230167696441)
        ·
          refine ⟨141389713244649172625772331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188519617659532230167696441 141389713244649172625772331)
          ·
            refine ⟨212084569866973758938658497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141389713244649172625772331 212084569866973758938658497)
            ·
              refine ⟨159063427400230319203993873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212084569866973758938658497 159063427400230319203993873)
              ·
                refine ⟨119297570550172739402995405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159063427400230319203993873 119297570550172739402995405)
                ·
                  refine ⟨44736588956314777276123277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119297570550172739402995405 44736588956314777276123277)
                  ·
                    refine ⟨16776220858618041478546229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44736588956314777276123277 16776220858618041478546229)
                    ·
                      refine ⟨1572770705495441388613709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16776220858618041478546229 1572770705495441388613709)
                      ·
                        rfl

theorem cell23_3062960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3062960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062960 prefixEnd_3062960 := by exact prefixLift 3062960
  have htrace : WordTrace (prefixWord ++ tailWord_3062960) baseStart_3062960 baseEnd_3062960 := by
    simpa [prefixWord, tailWord_3062960, baseEnd_3062960] using wordTrace_append hprefix tailTrace_3062960
  have hstable : (prefixWord ++ tailWord_3062960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062960).length < 2 ^ (prefixWord ++ tailWord_3062960).sum := by decide
  have hdescent : baseEnd_3062960 < baseStart_3062960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3062961 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3062961 : Nat := 118140960795 + 3062961 * 2 ^ 59
def prefixEnd_3062961 : Nat := 4983230072969 + 3 ^ 40 * 3062961 * 2
def baseEnd_3062961 : Nat := 1572771218976095884701205

theorem tailTrace_3062961 : CollatzResearch.WordTrace tailWord_3062961 prefixEnd_3062961 1572771218976095884701205 := by
  unfold tailWord_3062961
  simp only [CollatzResearch.WordTrace]
  refine ⟨111715365456422883936828737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74476910304281922624552491 111715365456422883936828737)
  ·
    refine ⟨83786524092317162952621553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111715365456422883936828737 83786524092317162952621553)
    ·
      refine ⟨62839893069237872214466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83786524092317162952621553 62839893069237872214466165)
      ·
        refine ⟨5891239975241050520106203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62839893069237872214466165 5891239975241050520106203)
        ·
          refine ⟨8836859962861575780159305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891239975241050520106203 8836859962861575780159305)
          ·
            refine ⟨6627644972146181835119479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836859962861575780159305 6627644972146181835119479)
            ·
              refine ⟨9941467458219272752679219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627644972146181835119479 9941467458219272752679219)
              ·
                refine ⟨14912201187328909129018829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941467458219272752679219 14912201187328909129018829)
                ·
                  refine ⟨5592075445248340923382061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14912201187328909129018829 5592075445248340923382061)
                  ·
                    refine ⟨2097028291968127846268273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5592075445248340923382061 2097028291968127846268273)
                    ·
                      refine ⟨1572771218976095884701205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097028291968127846268273 1572771218976095884701205)
                      ·
                        rfl

theorem cell23_3062961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3062961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3062961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3062961 prefixEnd_3062961 := by exact prefixLift 3062961
  have htrace : WordTrace (prefixWord ++ tailWord_3062961) baseStart_3062961 baseEnd_3062961 := by
    simpa [prefixWord, tailWord_3062961, baseEnd_3062961] using wordTrace_append hprefix tailTrace_3062961
  have hstable : (prefixWord ++ tailWord_3062961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3062961).length < 2 ^ (prefixWord ++ tailWord_3062961).sum := by decide
  have hdescent : baseEnd_3062961 < baseStart_3062961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3062961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063007 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3063007 : Nat := 118140960795 + 3063007 * 2 ^ 59
def prefixEnd_3063007 : Nat := 4983230072969 + 3 ^ 40 * 3063007 * 2
def baseEnd_3063007 : Nat := 1572794839086202704725993

theorem tailTrace_3063007 : CollatzResearch.WordTrace tailWord_3063007 prefixEnd_3063007 1572794839086202704725993 := by
  unfold tailWord_3063007
  simp only [CollatzResearch.WordTrace]
  refine ⟨111717043214256233793003275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74478028809504155862002183 111717043214256233793003275)
  ·
    refine ⟨167575564821384350689504913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111717043214256233793003275 167575564821384350689504913)
    ·
      refine ⟨125681673616038263017128685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167575564821384350689504913 125681673616038263017128685)
      ·
        refine ⟨47130627606014348631423257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125681673616038263017128685 47130627606014348631423257)
        ·
          refine ⟨35347970704510761473567443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47130627606014348631423257 35347970704510761473567443)
          ·
            refine ⟨53021956056766142210351165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35347970704510761473567443 53021956056766142210351165)
            ·
              refine ⟨19883233521287303328881687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53021956056766142210351165 19883233521287303328881687)
              ·
                refine ⟨29824850281930954993322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19883233521287303328881687 29824850281930954993322531)
                ·
                  refine ⟨44737275422896432489983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29824850281930954993322531 44737275422896432489983797)
                  ·
                    refine ⟨4194119570896540545935981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44737275422896432489983797 4194119570896540545935981)
                    ·
                      refine ⟨1572794839086202704725993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4194119570896540545935981 1572794839086202704725993)
                      ·
                        rfl

theorem cell23_3063007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3063007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063007 prefixEnd_3063007 := by exact prefixLift 3063007
  have htrace : WordTrace (prefixWord ++ tailWord_3063007) baseStart_3063007 baseEnd_3063007 := by
    simpa [prefixWord, tailWord_3063007, baseEnd_3063007] using wordTrace_append hprefix tailTrace_3063007
  have hstable : (prefixWord ++ tailWord_3063007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063007).length < 2 ^ (prefixWord ++ tailWord_3063007).sum := by decide
  have hdescent : baseEnd_3063007 < baseStart_3063007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063027 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 7]
def baseStart_3063027 : Nat := 118140960795 + 3063027 * 2 ^ 59
def prefixEnd_3063027 : Nat := 4983230072969 + 3 ^ 40 * 3063027 * 2
def baseEnd_3063027 : Nat := 524268369566430875491967

theorem tailTrace_3063027 : CollatzResearch.WordTrace tailWord_3063027 prefixEnd_3063027 524268369566430875491967 := by
  unfold tailWord_3063027
  simp only [CollatzResearch.WordTrace]
  refine ⟨111717772674183777208731335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74478515116122518139154223 111717772674183777208731335)
  ·
    refine ⟨167576659011275665813097003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111717772674183777208731335 167576659011275665813097003)
    ·
      refine ⟨251364988516913498719645505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167576659011275665813097003 251364988516913498719645505)
      ·
        refine ⟨188523741387685124039734129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251364988516913498719645505 188523741387685124039734129)
        ·
          refine ⟨141392806040763843029800597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188523741387685124039734129 141392806040763843029800597)
          ·
            refine ⟨6627787783160805142021903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141392806040763843029800597 6627787783160805142021903)
            ·
              refine ⟨9941681674741207713032855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627787783160805142021903 9941681674741207713032855)
              ·
                refine ⟨14912522512111811569549283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941681674741207713032855 14912522512111811569549283)
                ·
                  refine ⟨22368783768167717354323925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14912522512111811569549283 22368783768167717354323925)
                  ·
                    refine ⟨524268369566430875491967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22368783768167717354323925 524268369566430875491967)
                    ·
                      rfl

theorem cell23_3063027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_3063027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063027 prefixEnd_3063027 := by exact prefixLift 3063027
  have htrace : WordTrace (prefixWord ++ tailWord_3063027) baseStart_3063027 baseEnd_3063027 := by
    simpa [prefixWord, tailWord_3063027, baseEnd_3063027] using wordTrace_append hprefix tailTrace_3063027
  have hstable : (prefixWord ++ tailWord_3063027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063027).length < 2 ^ (prefixWord ++ tailWord_3063027).sum := by decide
  have hdescent : baseEnd_3063027 < baseStart_3063027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063042 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3063042 : Nat := 118140960795 + 3063042 * 2 ^ 59
def prefixEnd_3063042 : Nat := 4983230072969 + 3 ^ 40 * 3063042 * 2
def baseEnd_3063042 : Nat := 1572812810909110067788333

theorem tailTrace_3063042 : CollatzResearch.WordTrace tailWord_3063042 prefixEnd_3063042 1572812810909110067788333 := by
  unfold tailWord_3063042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27929579942282358692631845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74478879846086289847018253 27929579942282358692631845)
  ·
    refine ⟨5236796239177942254868471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27929579942282358692631845 5236796239177942254868471)
    ·
      refine ⟨7855194358766913382302707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236796239177942254868471 7855194358766913382302707)
      ·
        refine ⟨11782791538150370073454061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7855194358766913382302707 11782791538150370073454061)
        ·
          refine ⟨4418546826806388777545273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11782791538150370073454061 4418546826806388777545273)
          ·
            refine ⟨3313910120104791583158955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4418546826806388777545273 3313910120104791583158955)
            ·
              refine ⟨4970865180157187374738433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313910120104791583158955 4970865180157187374738433)
              ·
                refine ⟨3728148885117890531053825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970865180157187374738433 3728148885117890531053825)
                ·
                  refine ⟨2796111663838417898290369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728148885117890531053825 2796111663838417898290369)
                  ·
                    refine ⟨2097083747878813423717777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2796111663838417898290369 2097083747878813423717777)
                    ·
                      refine ⟨1572812810909110067788333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097083747878813423717777 1572812810909110067788333)
                      ·
                        rfl

theorem cell23_3063042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3063042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063042 prefixEnd_3063042 := by exact prefixLift 3063042
  have htrace : WordTrace (prefixWord ++ tailWord_3063042) baseStart_3063042 baseEnd_3063042 := by
    simpa [prefixWord, tailWord_3063042, baseEnd_3063042] using wordTrace_append hprefix tailTrace_3063042
  have hstable : (prefixWord ++ tailWord_3063042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063042).length < 2 ^ (prefixWord ++ tailWord_3063042).sum := by decide
  have hdescent : baseEnd_3063042 < baseStart_3063042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063084 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_3063084 : Nat := 118140960795 + 3063084 * 2 ^ 59
def prefixEnd_3063084 : Nat := 4983230072969 + 3 ^ 40 * 3063084 * 2
def baseEnd_3063084 : Nat := 1572834377096598903463139

theorem tailTrace_3063084 : CollatzResearch.WordTrace tailWord_3063084 prefixEnd_3063084 1572834377096598903463139 := by
  unfold tailWord_3063084
  simp only [CollatzResearch.WordTrace]
  refine ⟨55859925817488637971778153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74479901089984850629037537 55859925817488637971778153)
  ·
    refine ⟨41894944363116478478833615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55859925817488637971778153 41894944363116478478833615)
    ·
      refine ⟨62842416544674717718250423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41894944363116478478833615 62842416544674717718250423)
      ·
        refine ⟨94263624817012076577375635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62842416544674717718250423 94263624817012076577375635)
        ·
          refine ⟨141395437225518114866063453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94263624817012076577375635 141395437225518114866063453)
          ·
            refine ⟨53023288959569293074773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141395437225518114866063453 53023288959569293074773795)
            ·
              refine ⟨79534933439353939612160693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53023288959569293074773795 79534933439353939612160693)
              ·
                refine ⟨7456400009939431838640065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79534933439353939612160693 7456400009939431838640065)
                ·
                  refine ⟨5592300007454573878980049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7456400009939431838640065 5592300007454573878980049)
                  ·
                    refine ⟨4194225005590930409235037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592300007454573878980049 4194225005590930409235037)
                    ·
                      refine ⟨1572834377096598903463139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4194225005590930409235037 1572834377096598903463139)
                      ·
                        rfl

theorem cell23_3063084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_3063084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063084 prefixEnd_3063084 := by exact prefixLift 3063084
  have htrace : WordTrace (prefixWord ++ tailWord_3063084) baseStart_3063084 baseEnd_3063084 := by
    simpa [prefixWord, tailWord_3063084, baseEnd_3063084] using wordTrace_append hprefix tailTrace_3063084
  have hstable : (prefixWord ++ tailWord_3063084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063084).length < 2 ^ (prefixWord ++ tailWord_3063084).sum := by decide
  have hdescent : baseEnd_3063084 < baseStart_3063084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063108 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3063108 : Nat := 118140960795 + 3063108 * 2 ^ 59
def prefixEnd_3063108 : Nat := 4983230072969 + 3 ^ 40 * 3063108 * 2
def baseEnd_3063108 : Nat := 524282233544102269854343

theorem tailTrace_3063108 : CollatzResearch.WordTrace tailWord_3063108 prefixEnd_3063108 524282233544102269854343 := by
  unfold tailWord_3063108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55860363493445164021214989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74480484657926885361619985 55860363493445164021214989)
  ·
    refine ⟨20947636310041936507955621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55860363493445164021214989 20947636310041936507955621)
    ·
      refine ⟨3927681808132863095241679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20947636310041936507955621 3927681808132863095241679)
      ·
        refine ⟨5891522712199294642862519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927681808132863095241679 5891522712199294642862519)
        ·
          refine ⟨8837284068298941964293779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891522712199294642862519 8837284068298941964293779)
          ·
            refine ⟨13255926102448412946440669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837284068298941964293779 13255926102448412946440669)
            ·
              refine ⟨4970972288418154854915251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13255926102448412946440669 4970972288418154854915251)
              ·
                refine ⟨7456458432627232282372877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970972288418154854915251 7456458432627232282372877)
                ·
                  refine ⟨2796171912235212105889829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7456458432627232282372877 2796171912235212105889829)
                  ·
                    refine ⟨524282233544102269854343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796171912235212105889829 524282233544102269854343)
                    ·
                      rfl

theorem cell23_3063108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3063108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063108 prefixEnd_3063108 := by exact prefixLift 3063108
  have htrace : WordTrace (prefixWord ++ tailWord_3063108) baseStart_3063108 baseEnd_3063108 := by
    simpa [prefixWord, tailWord_3063108, baseEnd_3063108] using wordTrace_append hprefix tailTrace_3063108
  have hstable : (prefixWord ++ tailWord_3063108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063108).length < 2 ^ (prefixWord ++ tailWord_3063108).sum := by decide
  have hdescent : baseEnd_3063108 < baseStart_3063108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063151 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 1, 5]
def baseStart_3063151 : Nat := 118140960795 + 3063151 * 2 ^ 59
def prefixEnd_3063151 : Nat := 4983230072969 + 3 ^ 40 * 3063151 * 2
def baseEnd_3063151 : Nat := 524289593433483380441777

theorem tailTrace_3063151 : CollatzResearch.WordTrace tailWord_3063151 prefixEnd_3063151 524289593433483380441777 := by
  unfold tailWord_3063151
  simp only [CollatzResearch.WordTrace]
  refine ⟨111722295325734546386245307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74481530217156364257496871 111722295325734546386245307)
  ·
    refine ⟨167583442988601819579367961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111722295325734546386245307 167583442988601819579367961)
    ·
      refine ⟨125687582241451364684525971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167583442988601819579367961 125687582241451364684525971)
      ·
        refine ⟨188531373362177047026788957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125687582241451364684525971 188531373362177047026788957)
        ·
          refine ⟨70699265010816392635045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188531373362177047026788957 70699265010816392635045859)
          ·
            refine ⟨106048897516224588952568789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70699265010816392635045859 106048897516224588952568789)
            ·
              refine ⟨2485521035536513803575831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106048897516224588952568789 2485521035536513803575831)
              ·
                refine ⟨3728281553304770705363747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485521035536513803575831 3728281553304770705363747)
                ·
                  refine ⟨5592422329957156058045621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728281553304770705363747 5592422329957156058045621)
                  ·
                    refine ⟨524289593433483380441777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5592422329957156058045621 524289593433483380441777)
                    ·
                      rfl

theorem cell23_3063151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_3063151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063151 prefixEnd_3063151 := by exact prefixLift 3063151
  have htrace : WordTrace (prefixWord ++ tailWord_3063151) baseStart_3063151 baseEnd_3063151 := by
    simpa [prefixWord, tailWord_3063151, baseEnd_3063151] using wordTrace_append hprefix tailTrace_3063151
  have hstable : (prefixWord ++ tailWord_3063151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063151).length < 2 ^ (prefixWord ++ tailWord_3063151).sum := by decide
  have hdescent : baseEnd_3063151 < baseStart_3063151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063187 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_3063187 : Nat := 118140960795 + 3063187 * 2 ^ 59
def prefixEnd_3063187 : Nat := 4983230072969 + 3 ^ 40 * 3063187 * 2
def baseEnd_3063187 : Nat := 1572887265604012000475165

theorem tailTrace_3063187 : CollatzResearch.WordTrace tailWord_3063187 prefixEnd_3063187 1572887265604012000475165 := by
  unfold tailWord_3063187
  simp only [CollatzResearch.WordTrace]
  refine ⟨111723608353604124534555815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74482405569069416356370543 111723608353604124534555815)
  ·
    refine ⟨167585412530406186801833723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111723608353604124534555815 167585412530406186801833723)
    ·
      refine ⟨251378118795609280202750585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167585412530406186801833723 251378118795609280202750585)
      ·
        refine ⟨188533589096706960152062939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251378118795609280202750585 188533589096706960152062939)
        ·
          refine ⟨282800383645060440228094409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188533589096706960152062939 282800383645060440228094409)
          ·
            refine ⟨212100287733795330171070807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282800383645060440228094409 212100287733795330171070807)
            ·
              refine ⟨318150431600692995256606211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212100287733795330171070807 318150431600692995256606211)
              ·
                refine ⟨477225647401039492884909317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318150431600692995256606211 477225647401039492884909317)
                ·
                  refine ⟨89479808887694904915920497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477225647401039492884909317 89479808887694904915920497)
                  ·
                    refine ⟨67109856665771178686940373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89479808887694904915920497 67109856665771178686940373)
                    ·
                      refine ⟨1572887265604012000475165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67109856665771178686940373 1572887265604012000475165)
                      ·
                        rfl

theorem cell23_3063187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_3063187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063187 prefixEnd_3063187 := by exact prefixLift 3063187
  have htrace : WordTrace (prefixWord ++ tailWord_3063187) baseStart_3063187 baseEnd_3063187 := by
    simpa [prefixWord, tailWord_3063187, baseEnd_3063187] using wordTrace_append hprefix tailTrace_3063187
  have hstable : (prefixWord ++ tailWord_3063187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063187).length < 2 ^ (prefixWord ++ tailWord_3063187).sum := by decide
  have hdescent : baseEnd_3063187 < baseStart_3063187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063191 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3063191 : Nat := 118140960795 + 3063191 * 2 ^ 59
def prefixEnd_3063191 : Nat := 4983230072969 + 3 ^ 40 * 3063191 * 2
def baseEnd_3063191 : Nat := 1572889319526629984825147

theorem tailTrace_3063191 : CollatzResearch.WordTrace tailWord_3063191 prefixEnd_3063191 1572889319526629984825147 := by
  unfold tailWord_3063191
  simp only [CollatzResearch.WordTrace]
  refine ⟨111723754245589633217701427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74482502830393088811800951 111723754245589633217701427)
  ·
    refine ⟨167585631368384449826552141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111723754245589633217701427 167585631368384449826552141)
    ·
      refine ⟨62844611763144168684957053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167585631368384449826552141 62844611763144168684957053)
      ·
        refine ⟨23566729411179063256858895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62844611763144168684957053 23566729411179063256858895)
        ·
          refine ⟨35350094116768594885288343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23566729411179063256858895 35350094116768594885288343)
          ·
            refine ⟨53025141175152892327932515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35350094116768594885288343 53025141175152892327932515)
            ·
              refine ⟨79537711762729338491898773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53025141175152892327932515 79537711762729338491898773)
              ·
                refine ⟨3728330238877937741807755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79537711762729338491898773 3728330238877937741807755)
                ·
                  refine ⟨5592495358316906612711633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728330238877937741807755 5592495358316906612711633)
                  ·
                    refine ⟨4194371518737679959533725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592495358316906612711633 4194371518737679959533725)
                    ·
                      refine ⟨1572889319526629984825147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4194371518737679959533725 1572889319526629984825147)
                      ·
                        rfl

theorem cell23_3063191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3063191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063191 prefixEnd_3063191 := by exact prefixLift 3063191
  have htrace : WordTrace (prefixWord ++ tailWord_3063191) baseStart_3063191 baseEnd_3063191 := by
    simpa [prefixWord, tailWord_3063191, baseEnd_3063191] using wordTrace_append hprefix tailTrace_3063191
  have hstable : (prefixWord ++ tailWord_3063191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063191).length < 2 ^ (prefixWord ++ tailWord_3063191).sum := by decide
  have hdescent : baseEnd_3063191 < baseStart_3063191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3063192 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3063192 : Nat := 118140960795 + 3063192 * 2 ^ 59
def prefixEnd_3063192 : Nat := 4983230072969 + 3 ^ 40 * 3063192 * 2
def baseEnd_3063192 : Nat := 1572889833007284480912643

theorem tailTrace_3063192 : CollatzResearch.WordTrace tailWord_3063192 prefixEnd_3063192 1572889833007284480912643 := by
  unfold tailWord_3063192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55861895359293005194243915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74482527145724006925658553 55861895359293005194243915)
  ·
    refine ⟨83792843038939507791365873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55861895359293005194243915 83792843038939507791365873)
    ·
      refine ⟨62844632279204630843524405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83792843038939507791365873 62844632279204630843524405)
      ·
        refine ⟨5891684276175434141580413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62844632279204630843524405 5891684276175434141580413)
        ·
          refine ⟨2209381603565787803092655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5891684276175434141580413 2209381603565787803092655)
          ·
            refine ⟨3314072405348681704638983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209381603565787803092655 3314072405348681704638983)
            ·
              refine ⟨4971108608023022556958475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314072405348681704638983 4971108608023022556958475)
              ·
                refine ⟨7456662912034533835437713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971108608023022556958475 7456662912034533835437713)
                ·
                  refine ⟨5592497184025900376578285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7456662912034533835437713 5592497184025900376578285)
                  ·
                    refine ⟨2097186444009712641216857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5592497184025900376578285 2097186444009712641216857)
                    ·
                      refine ⟨1572889833007284480912643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2097186444009712641216857 1572889833007284480912643)
                      ·
                        rfl

theorem cell23_3063192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3063192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3063192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3063192 prefixEnd_3063192 := by exact prefixLift 3063192
  have htrace : WordTrace (prefixWord ++ tailWord_3063192) baseStart_3063192 baseEnd_3063192 := by
    simpa [prefixWord, tailWord_3063192, baseEnd_3063192] using wordTrace_append hprefix tailTrace_3063192
  have hstable : (prefixWord ++ tailWord_3063192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3063192).length < 2 ^ (prefixWord ++ tailWord_3063192).sum := by decide
  have hdescent : baseEnd_3063192 < baseStart_3063192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3063192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
