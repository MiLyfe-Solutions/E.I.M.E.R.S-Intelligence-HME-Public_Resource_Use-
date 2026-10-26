import V185TrunkScan23Chunk0938

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5558328 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_5558328 : Nat := 118140960795 + 5558328 * 2 ^ 59
def prefixEnd_5558328 : Nat := 4983230072969 + 3 ^ 40 * 5558328 * 2
def baseEnd_5558328 : Nat := 2854093899344034249837721

theorem tailTrace_5558328 : CollatzResearch.WordTrace tailWord_5558328 prefixEnd_5558328 2854093899344034249837721 := by
  unfold tailWord_5558328
  simp only [CollatzResearch.WordTrace]
  refine ⟨101364438503567208845461819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135152584671422945127282425 101364438503567208845461819)
  ·
    refine ⟨152046657755350813268192729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101364438503567208845461819 152046657755350813268192729)
    ·
      refine ⟨114034993316513109951144547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152046657755350813268192729 114034993316513109951144547)
      ·
        refine ⟨171052489974769664926716821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114034993316513109951144547 171052489974769664926716821)
        ·
          refine ⟨8018085467567328043439851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171052489974769664926716821 8018085467567328043439851)
          ·
            refine ⟨12027128201350992065159777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8018085467567328043439851 12027128201350992065159777)
            ·
              refine ⟨9020346151013244048869833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12027128201350992065159777 9020346151013244048869833)
              ·
                refine ⟨6765259613259933036652375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020346151013244048869833 6765259613259933036652375)
                ·
                  refine ⟨10147889419889899554978563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765259613259933036652375 10147889419889899554978563)
                  ·
                    refine ⟨15221834129834849332467845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10147889419889899554978563 15221834129834849332467845)
                    ·
                      refine ⟨2854093899344034249837721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15221834129834849332467845 2854093899344034249837721)
                      ·
                        rfl

theorem cell23_5558328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_5558328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558328 prefixEnd_5558328 := by exact prefixLift 5558328
  have htrace : WordTrace (prefixWord ++ tailWord_5558328) baseStart_5558328 baseEnd_5558328 := by
    simpa [prefixWord, tailWord_5558328, baseEnd_5558328] using wordTrace_append hprefix tailTrace_5558328
  have hstable : (prefixWord ++ tailWord_5558328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558328).length < 2 ^ (prefixWord ++ tailWord_5558328).sum := by decide
  have hdescent : baseEnd_5558328 < baseStart_5558328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558358 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5558358 : Nat := 118140960795 + 5558358 * 2 ^ 59
def prefixEnd_5558358 : Nat := 4983230072969 + 3 ^ 40 * 5558358 * 2
def baseEnd_5558358 : Nat := 2854109303763669132462583

theorem tailTrace_5558358 : CollatzResearch.WordTrace tailWord_5558358 prefixEnd_5558358 2854109303763669132462583 := by
  unfold tailWord_5558358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670623199814108300907233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135153314131350488543010485 12670623199814108300907233)
  ·
    refine ⟨9502967399860581225680425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12670623199814108300907233 9502967399860581225680425)
    ·
      refine ⟨7127225549895435919260319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9502967399860581225680425 7127225549895435919260319)
      ·
        refine ⟨10690838324843153878890479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127225549895435919260319 10690838324843153878890479)
        ·
          refine ⟨16036257487264730818335719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690838324843153878890479 16036257487264730818335719)
          ·
            refine ⟨24054386230897096227503579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036257487264730818335719 24054386230897096227503579)
            ·
              refine ⟨36081579346345644341255369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24054386230897096227503579 36081579346345644341255369)
              ·
                refine ⟨27061184509759233255941527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36081579346345644341255369 27061184509759233255941527)
                ·
                  refine ⟨40591776764638849883912291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27061184509759233255941527 40591776764638849883912291)
                  ·
                    refine ⟨60887665146958274825868437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40591776764638849883912291 60887665146958274825868437)
                    ·
                      refine ⟨2854109303763669132462583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60887665146958274825868437 2854109303763669132462583)
                      ·
                        rfl

theorem cell23_5558358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5558358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558358 prefixEnd_5558358 := by exact prefixLift 5558358
  have htrace : WordTrace (prefixWord ++ tailWord_5558358) baseStart_5558358 baseEnd_5558358 := by
    simpa [prefixWord, tailWord_5558358, baseEnd_5558358] using wordTrace_append hprefix tailTrace_5558358
  have hstable : (prefixWord ++ tailWord_5558358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558358).length < 2 ^ (prefixWord ++ tailWord_5558358).sum := by decide
  have hdescent : baseEnd_5558358 < baseStart_5558358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558361 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_5558361 : Nat := 118140960795 + 5558361 * 2 ^ 59
def prefixEnd_5558361 : Nat := 4983230072969 + 3 ^ 40 * 5558361 * 2
def baseEnd_5558361 : Nat := 2854110844205632620725069

theorem tailTrace_5558361 : CollatzResearch.WordTrace tailWord_5558361 prefixEnd_5558361 2854110844205632620725069 := by
  unfold tailWord_5558361
  simp only [CollatzResearch.WordTrace]
  refine ⟨202730080616014864326874937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135153387077343242884583291 202730080616014864326874937)
  ·
    refine ⟨152047560462011148245156203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202730080616014864326874937 152047560462011148245156203)
    ·
      refine ⟨228071340693016722367734305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152047560462011148245156203 228071340693016722367734305)
      ·
        refine ⟨171053505519762541775800729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228071340693016722367734305 171053505519762541775800729)
        ·
          refine ⟨128290129139821906331850547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171053505519762541775800729 128290129139821906331850547)
          ·
            refine ⟨192435193709732859497775821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128290129139821906331850547 192435193709732859497775821)
            ·
              refine ⟨72163197641149822311665933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192435193709732859497775821 72163197641149822311665933)
              ·
                refine ⟨27061199115431183366874725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72163197641149822311665933 27061199115431183366874725)
                ·
                  refine ⟨5073974834143346881289011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27061199115431183366874725 5073974834143346881289011)
                  ·
                    refine ⟨7610962251215020321933517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5073974834143346881289011 7610962251215020321933517)
                    ·
                      refine ⟨2854110844205632620725069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610962251215020321933517 2854110844205632620725069)
                      ·
                        rfl

theorem cell23_5558361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_5558361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558361 prefixEnd_5558361 := by exact prefixLift 5558361
  have htrace : WordTrace (prefixWord ++ tailWord_5558361) baseStart_5558361 baseEnd_5558361 := by
    simpa [prefixWord, tailWord_5558361, baseEnd_5558361] using wordTrace_append hprefix tailTrace_5558361
  have hstable : (prefixWord ++ tailWord_5558361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558361).length < 2 ^ (prefixWord ++ tailWord_5558361).sum := by decide
  have hdescent : baseEnd_5558361 < baseStart_5558361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558362 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_5558362 : Nat := 118140960795 + 5558362 * 2 ^ 59
def prefixEnd_5558362 : Nat := 4983230072969 + 3 ^ 40 * 5558362 * 2
def baseEnd_5558362 : Nat := 2854111357686287116812565

theorem tailTrace_5558362 : CollatzResearch.WordTrace tailWord_5558362 prefixEnd_5558362 2854111357686287116812565 := by
  unfold tailWord_5558362
  simp only [CollatzResearch.WordTrace]
  refine ⟨50682529272252810374415335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135153411392674160998440893 50682529272252810374415335)
  ·
    refine ⟨76023793908379215561623003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50682529272252810374415335 76023793908379215561623003)
    ·
      refine ⟨114035690862568823342434505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76023793908379215561623003 114035690862568823342434505)
      ·
        refine ⟨85526768146926617506825879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114035690862568823342434505 85526768146926617506825879)
        ·
          refine ⟨128290152220389926260238819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85526768146926617506825879 128290152220389926260238819)
          ·
            refine ⟨192435228330584889390358229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128290152220389926260238819 192435228330584889390358229)
            ·
              refine ⟨4510200663998083345086521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 192435228330584889390358229 4510200663998083345086521)
              ·
                refine ⟨3382650497998562508814891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510200663998083345086521 3382650497998562508814891)
                ·
                  refine ⟨5073975746997843763222337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382650497998562508814891 5073975746997843763222337)
                  ·
                    refine ⟨3805481810248382822416753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073975746997843763222337 3805481810248382822416753)
                    ·
                      refine ⟨2854111357686287116812565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805481810248382822416753 2854111357686287116812565)
                      ·
                        rfl

theorem cell23_5558362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_5558362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558362 prefixEnd_5558362 := by exact prefixLift 5558362
  have htrace : WordTrace (prefixWord ++ tailWord_5558362) baseStart_5558362 baseEnd_5558362 := by
    simpa [prefixWord, tailWord_5558362, baseEnd_5558362] using wordTrace_append hprefix tailTrace_5558362
  have hstable : (prefixWord ++ tailWord_5558362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558362).length < 2 ^ (prefixWord ++ tailWord_5558362).sum := by decide
  have hdescent : baseEnd_5558362 < baseStart_5558362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558418 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5558418 : Nat := 118140960795 + 5558418 * 2 ^ 59
def prefixEnd_5558418 : Nat := 4983230072969 + 3 ^ 40 * 5558418 * 2
def baseEnd_5558418 : Nat := 2854140112602938897712307

theorem tailTrace_5558418 : CollatzResearch.WordTrace tailWord_5558418 prefixEnd_5558418 2854140112602938897712307 := by
  unfold tailWord_5558418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50683039894202090765424977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135154773051205575374466605 50683039894202090765424977)
  ·
    refine ⟨38012279920651568074068733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50683039894202090765424977 38012279920651568074068733)
    ·
      refine ⟨14254604970244338027775775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38012279920651568074068733 14254604970244338027775775)
      ·
        refine ⟨21381907455366507041663663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14254604970244338027775775 21381907455366507041663663)
        ·
          refine ⟨32072861183049760562495495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21381907455366507041663663 32072861183049760562495495)
          ·
            refine ⟨48109291774574640843743243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32072861183049760562495495 48109291774574640843743243)
            ·
              refine ⟨72163937661861961265614865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48109291774574640843743243 72163937661861961265614865)
              ·
                refine ⟨54122953246396470949211149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72163937661861961265614865 54122953246396470949211149)
                ·
                  refine ⟨20296107467398676605954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54122953246396470949211149 20296107467398676605954181)
                  ·
                    refine ⟨3805520150137251863616409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20296107467398676605954181 3805520150137251863616409)
                    ·
                      refine ⟨2854140112602938897712307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805520150137251863616409 2854140112602938897712307)
                      ·
                        rfl

theorem cell23_5558418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5558418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558418 prefixEnd_5558418 := by exact prefixLift 5558418
  have htrace : WordTrace (prefixWord ++ tailWord_5558418) baseStart_5558418 baseEnd_5558418 := by
    simpa [prefixWord, tailWord_5558418, baseEnd_5558418] using wordTrace_append hprefix tailTrace_5558418
  have hstable : (prefixWord ++ tailWord_5558418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558418).length < 2 ^ (prefixWord ++ tailWord_5558418).sum := by decide
  have hdescent : baseEnd_5558418 < baseStart_5558418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558431 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5558431 : Nat := 118140960795 + 5558431 * 2 ^ 59
def prefixEnd_5558431 : Nat := 4983230072969 + 3 ^ 40 * 5558431 * 2
def baseEnd_5558431 : Nat := 2854146787851447346849747

theorem tailTrace_5558431 : CollatzResearch.WordTrace tailWord_5558431 prefixEnd_5558431 2854146787851447346849747 := by
  unfold tailWord_5558431
  simp only [CollatzResearch.WordTrace]
  refine ⟨202732633725761266281923147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135155089150507510854615431 202732633725761266281923147)
  ·
    refine ⟨304098950588641899422884721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202732633725761266281923147 304098950588641899422884721)
    ·
      refine ⟨228074212941481424567163541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304098950588641899422884721 228074212941481424567163541)
      ·
        refine ⟨10690978731631941776585791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228074212941481424567163541 10690978731631941776585791)
        ·
          refine ⟨16036468097447912664878687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690978731631941776585791 16036468097447912664878687)
          ·
            refine ⟨24054702146171868997318031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036468097447912664878687 24054702146171868997318031)
            ·
              refine ⟨36082053219257803495977047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24054702146171868997318031 36082053219257803495977047)
              ·
                refine ⟨54123079828886705243965571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36082053219257803495977047 54123079828886705243965571)
                ·
                  refine ⟨81184619743330057865948357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54123079828886705243965571 81184619743330057865948357)
                  ·
                    refine ⟨15222116201874385849865317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81184619743330057865948357 15222116201874385849865317)
                    ·
                      refine ⟨2854146787851447346849747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15222116201874385849865317 2854146787851447346849747)
                      ·
                        rfl

theorem cell23_5558431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5558431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558431 prefixEnd_5558431 := by exact prefixLift 5558431
  have htrace : WordTrace (prefixWord ++ tailWord_5558431) baseStart_5558431 baseEnd_5558431 := by
    simpa [prefixWord, tailWord_5558431, baseEnd_5558431] using wordTrace_append hprefix tailTrace_5558431
  have hstable : (prefixWord ++ tailWord_5558431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558431).length < 2 ^ (prefixWord ++ tailWord_5558431).sum := by decide
  have hdescent : baseEnd_5558431 < baseStart_5558431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558468 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_5558468 : Nat := 118140960795 + 5558468 * 2 ^ 59
def prefixEnd_5558468 : Nat := 4983230072969 + 3 ^ 40 * 5558468 * 2
def baseEnd_5558468 : Nat := 2854165786635663702087077

theorem tailTrace_5558468 : CollatzResearch.WordTrace tailWord_5558468 prefixEnd_5558468 2854165786635663702087077 := by
  unfold tailWord_5558468
  simp only [CollatzResearch.WordTrace]
  refine ⟨101366991613313610800510029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135155988817751481067346705 101366991613313610800510029)
  ·
    refine ⟨38012621854992604050191261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101366991613313610800510029 38012621854992604050191261)
    ·
      refine ⟨14254733195622226518821723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38012621854992604050191261 14254733195622226518821723)
      ·
        refine ⟨21382099793433339778232585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14254733195622226518821723 21382099793433339778232585)
        ·
          refine ⟨16036574845075004833674439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21382099793433339778232585 16036574845075004833674439)
          ·
            refine ⟨24054862267612507250511659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036574845075004833674439 24054862267612507250511659)
            ·
              refine ⟨36082293401418760875767489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24054862267612507250511659 36082293401418760875767489)
              ·
                refine ⟨27061720051064070656825617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36082293401418760875767489 27061720051064070656825617)
                ·
                  refine ⟨20296290038298052992619213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27061720051064070656825617 20296290038298052992619213)
                  ·
                    refine ⟨7611108764361769872232205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20296290038298052992619213 7611108764361769872232205)
                    ·
                      refine ⟨2854165786635663702087077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611108764361769872232205 2854165786635663702087077)
                      ·
                        rfl

theorem cell23_5558468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_5558468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558468 prefixEnd_5558468 := by exact prefixLift 5558468
  have htrace : WordTrace (prefixWord ++ tailWord_5558468) baseStart_5558468 baseEnd_5558468 := by
    simpa [prefixWord, tailWord_5558468, baseEnd_5558468] using wordTrace_append hprefix tailTrace_5558468
  have hstable : (prefixWord ++ tailWord_5558468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558468).length < 2 ^ (prefixWord ++ tailWord_5558468).sum := by decide
  have hdescent : baseEnd_5558468 < baseStart_5558468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558486 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5558486 : Nat := 118140960795 + 5558486 * 2 ^ 59
def prefixEnd_5558486 : Nat := 4983230072969 + 3 ^ 40 * 5558486 * 2
def baseEnd_5558486 : Nat := 2854175029287444631661995

theorem tailTrace_5558486 : CollatzResearch.WordTrace tailWord_5558486 prefixEnd_5558486 2854175029287444631661995 := by
  unfold tailWord_5558486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670914983785125667198457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135156426493708007116783541 12670914983785125667198457)
  ·
    refine ⟨9503186237838844250398843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12670914983785125667198457 9503186237838844250398843)
    ·
      refine ⟨14254779356758266375598265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503186237838844250398843 14254779356758266375598265)
      ·
        refine ⟨10691084517568699781698699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14254779356758266375598265 10691084517568699781698699)
        ·
          refine ⟨16036626776353049672548049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691084517568699781698699 16036626776353049672548049)
          ·
            refine ⟨12027470082264787254411037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16036626776353049672548049 12027470082264787254411037)
            ·
              refine ⟨4510301280849295220404139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12027470082264787254411037 4510301280849295220404139)
              ·
                refine ⟨6765451921273942830606209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510301280849295220404139 6765451921273942830606209)
                ·
                  refine ⟨5074088940955457122954657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765451921273942830606209 5074088940955457122954657)
                  ·
                    refine ⟨3805566705716592842215993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074088940955457122954657 3805566705716592842215993)
                    ·
                      refine ⟨2854175029287444631661995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805566705716592842215993 2854175029287444631661995)
                      ·
                        rfl

theorem cell23_5558486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5558486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558486 prefixEnd_5558486 := by exact prefixLift 5558486
  have htrace : WordTrace (prefixWord ++ tailWord_5558486) baseStart_5558486 baseEnd_5558486 := by
    simpa [prefixWord, tailWord_5558486, baseEnd_5558486] using wordTrace_append hprefix tailTrace_5558486
  have hstable : (prefixWord ++ tailWord_5558486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558486).length < 2 ^ (prefixWord ++ tailWord_5558486).sum := by decide
  have hdescent : baseEnd_5558486 < baseStart_5558486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558518 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_5558518 : Nat := 118140960795 + 5558518 * 2 ^ 59
def prefixEnd_5558518 : Nat := 4983230072969 + 3 ^ 40 * 5558518 * 2
def baseEnd_5558518 : Nat := 951397153556129502153949

theorem tailTrace_5558518 : CollatzResearch.WordTrace tailWord_5558518 prefixEnd_5558518 951397153556129502153949 := by
  unfold tailWord_5558518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670987929777880008771263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135157204584297386760226805 12670987929777880008771263)
  ·
    refine ⟨19006481894666820013156895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12670987929777880008771263 19006481894666820013156895)
    ·
      refine ⟨28509722842000230019735343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19006481894666820013156895 28509722842000230019735343)
      ·
        refine ⟨42764584263000345029603015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28509722842000230019735343 42764584263000345029603015)
        ·
          refine ⟨64146876394500517544404523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42764584263000345029603015 64146876394500517544404523)
          ·
            refine ⟨96220314591750776316606785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64146876394500517544404523 96220314591750776316606785)
            ·
              refine ⟨72165235943813082237455089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96220314591750776316606785 72165235943813082237455089)
              ·
                refine ⟨54123926957859811678091317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72165235943813082237455089 54123926957859811678091317)
                ·
                  refine ⟨5074118152299357344821061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54123926957859811678091317 5074118152299357344821061)
                  ·
                    refine ⟨951397153556129502153949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074118152299357344821061 951397153556129502153949)
                    ·
                      rfl

theorem cell23_5558518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_5558518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558518 prefixEnd_5558518 := by exact prefixLift 5558518
  have htrace : WordTrace (prefixWord ++ tailWord_5558518) baseStart_5558518 baseEnd_5558518 := by
    simpa [prefixWord, tailWord_5558518, baseEnd_5558518] using wordTrace_append hprefix tailTrace_5558518
  have hstable : (prefixWord ++ tailWord_5558518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558518).length < 2 ^ (prefixWord ++ tailWord_5558518).sum := by decide
  have hdescent : baseEnd_5558518 < baseStart_5558518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558531 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 6]
def baseStart_5558531 : Nat := 118140960795 + 5558531 * 2 ^ 59
def prefixEnd_5558531 : Nat := 4983230072969 + 3 ^ 40 * 5558531 * 2
def baseEnd_5558531 : Nat := 317133126212988550622143

theorem tailTrace_5558531 : CollatzResearch.WordTrace tailWord_5558531 prefixEnd_5558531 317133126212988550622143 := by
  unfold tailWord_5558531
  simp only [CollatzResearch.WordTrace]
  refine ⟨202736281025398983360563447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135157520683599322240375631 202736281025398983360563447)
  ·
    refine ⟨304104421538098475040845171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202736281025398983360563447 304104421538098475040845171)
    ·
      refine ⟨456156632307147712561267757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304104421538098475040845171 456156632307147712561267757)
      ·
        refine ⟨171058737115180392210475409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456156632307147712561267757 171058737115180392210475409)
        ·
          refine ⟨128294052836385294157856557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171058737115180392210475409 128294052836385294157856557)
          ·
            refine ⟨48110269813644485309196209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128294052836385294157856557 48110269813644485309196209)
            ·
              refine ⟨36082702360233363981897157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48110269813644485309196209 36082702360233363981897157)
              ·
                refine ⟨6765506692543755746605717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36082702360233363981897157 6765506692543755746605717)
                ·
                  refine ⟨317133126212988550622143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6765506692543755746605717 317133126212988550622143)
                  ·
                    rfl

theorem cell23_5558531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 6].length) (baseStart_5558531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558531 prefixEnd_5558531 := by exact prefixLift 5558531
  have htrace : WordTrace (prefixWord ++ tailWord_5558531) baseStart_5558531 baseEnd_5558531 := by
    simpa [prefixWord, tailWord_5558531, baseEnd_5558531] using wordTrace_append hprefix tailTrace_5558531
  have hstable : (prefixWord ++ tailWord_5558531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558531).length < 2 ^ (prefixWord ++ tailWord_5558531).sum := by decide
  have hdescent : baseEnd_5558531 < baseStart_5558531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558591 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 6]
def baseStart_5558591 : Nat := 118140960795 + 5558591 * 2 ^ 59
def prefixEnd_5558591 : Nat := 4983230072969 + 3 ^ 40 * 5558591 * 2
def baseEnd_5558591 : Nat := 951409648252055573616337

theorem tailTrace_5558591 : CollatzResearch.WordTrace tailWord_5558591 prefixEnd_5558591 951409648252055573616337 := by
  unfold tailWord_5558591
  simp only [CollatzResearch.WordTrace]
  refine ⟨202738469405181613607747627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135158979603454409071831751 202738469405181613607747627)
  ·
    refine ⟨304107704107772420411621441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202738469405181613607747627 304107704107772420411621441)
    ·
      refine ⟨228080778080829315308716081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304107704107772420411621441 228080778080829315308716081)
      ·
        refine ⟨171060583560621986481537061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228080778080829315308716081 171060583560621986481537061)
        ·
          refine ⟨32073859417616622465288199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171060583560621986481537061 32073859417616622465288199)
          ·
            refine ⟨48110789126424933697932299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32073859417616622465288199 48110789126424933697932299)
            ·
              refine ⟨72166183689637400546898449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48110789126424933697932299 72166183689637400546898449)
              ·
                refine ⟨54124637767228050410173837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72166183689637400546898449 54124637767228050410173837)
                ·
                  refine ⟨20296739162710518903815189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54124637767228050410173837 20296739162710518903815189)
                  ·
                    refine ⟨951409648252055573616337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20296739162710518903815189 951409648252055573616337)
                    ·
                      rfl

theorem cell23_5558591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_5558591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558591 prefixEnd_5558591 := by exact prefixLift 5558591
  have htrace : WordTrace (prefixWord ++ tailWord_5558591) baseStart_5558591 baseEnd_5558591 := by
    simpa [prefixWord, tailWord_5558591, baseEnd_5558591] using wordTrace_append hprefix tailTrace_5558591
  have hstable : (prefixWord ++ tailWord_5558591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558591).length < 2 ^ (prefixWord ++ tailWord_5558591).sum := by decide
  have hdescent : baseEnd_5558591 < baseStart_5558591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558601 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_5558601 : Nat := 118140960795 + 5558601 * 2 ^ 59
def prefixEnd_5558601 : Nat := 4983230072969 + 3 ^ 40 * 5558601 * 2
def baseEnd_5558601 : Nat := 2854234079562711681723965

theorem tailTrace_5558601 : CollatzResearch.WordTrace tailWord_5558601 prefixEnd_5558601 2854234079562711681723965 := by
  unfold tailWord_5558601
  simp only [CollatzResearch.WordTrace]
  refine ⟨202738834135145385315611657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135159222756763590210407771 202738834135145385315611657)
  ·
    refine ⟨152054125601359038986708743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202738834135145385315611657 152054125601359038986708743)
    ·
      refine ⟨228081188402038558480063115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152054125601359038986708743 228081188402038558480063115)
      ·
        refine ⟨342121782603057837720094673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228081188402038558480063115 342121782603057837720094673)
        ·
          refine ⟨256591336952293378290071005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342121782603057837720094673 256591336952293378290071005)
          ·
            refine ⟨96221751357110016858776627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256591336952293378290071005 96221751357110016858776627)
            ·
              refine ⟨144332627035665025288164941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96221751357110016858776627 144332627035665025288164941)
              ·
                refine ⟨54124735138374384483061853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144332627035665025288164941 54124735138374384483061853)
                ·
                  refine ⟨20296775676890394181148195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54124735138374384483061853 20296775676890394181148195)
                  ·
                    refine ⟨30445163515335591271722293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20296775676890394181148195 30445163515335591271722293)
                    ·
                      refine ⟨2854234079562711681723965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30445163515335591271722293 2854234079562711681723965)
                      ·
                        rfl

theorem cell23_5558601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_5558601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558601 prefixEnd_5558601 := by exact prefixLift 5558601
  have htrace : WordTrace (prefixWord ++ tailWord_5558601) baseStart_5558601 baseEnd_5558601 := by
    simpa [prefixWord, tailWord_5558601, baseEnd_5558601] using wordTrace_append hprefix tailTrace_5558601
  have hstable : (prefixWord ++ tailWord_5558601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558601).length < 2 ^ (prefixWord ++ tailWord_5558601).sum := by decide
  have hdescent : baseEnd_5558601 < baseStart_5558601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558608 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_5558608 : Nat := 118140960795 + 5558608 * 2 ^ 59
def prefixEnd_5558608 : Nat := 4983230072969 + 3 ^ 40 * 5558608 * 2
def baseEnd_5558608 : Nat := 951412557975764384778811

theorem tailTrace_5558608 : CollatzResearch.WordTrace tailWord_5558608 prefixEnd_5558608 951412557975764384778811 := by
  unfold tailWord_5558608
  simp only [CollatzResearch.WordTrace]
  refine ⟨101369544723060012755558239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135159392964080017007410985 101369544723060012755558239)
  ·
    refine ⟨152054317084590019133337359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101369544723060012755558239 152054317084590019133337359)
    ·
      refine ⟨228081475626885028700006039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152054317084590019133337359 228081475626885028700006039)
      ·
        refine ⟨342122213440327543050009059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228081475626885028700006039 342122213440327543050009059)
        ·
          refine ⟨513183320160491314575013589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342122213440327543050009059 513183320160491314575013589)
          ·
            refine ⟨12027734066261515185351881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 513183320160491314575013589 12027734066261515185351881)
            ·
              refine ⟨9020800549696136389013911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12027734066261515185351881 9020800549696136389013911)
              ·
                refine ⟨13531200824544204583520867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9020800549696136389013911 13531200824544204583520867)
                ·
                  refine ⟨20296801236816306875281301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13531200824544204583520867 20296801236816306875281301)
                  ·
                    refine ⟨951412557975764384778811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20296801236816306875281301 951412557975764384778811)
                    ·
                      rfl

theorem cell23_5558608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_5558608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558608 prefixEnd_5558608 := by exact prefixLift 5558608
  have htrace : WordTrace (prefixWord ++ tailWord_5558608) baseStart_5558608 baseEnd_5558608 := by
    simpa [prefixWord, tailWord_5558608, baseEnd_5558608] using wordTrace_append hprefix tailTrace_5558608
  have hstable : (prefixWord ++ tailWord_5558608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558608).length < 2 ^ (prefixWord ++ tailWord_5558608).sum := by decide
  have hdescent : baseEnd_5558608 < baseStart_5558608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558628 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_5558628 : Nat := 118140960795 + 5558628 * 2 ^ 59
def prefixEnd_5558628 : Nat := 4983230072969 + 3 ^ 40 * 5558628 * 2
def baseEnd_5558628 : Nat := 2854247943540383076086341

theorem tailTrace_5558628 : CollatzResearch.WordTrace tailWord_5558628 prefixEnd_5558628 2854247943540383076086341 := by
  unfold tailWord_5558628
  simp only [CollatzResearch.WordTrace]
  refine ⟨101369909453023784463422269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135159879270698379284563025 101369909453023784463422269)
  ·
    refine ⟨38013716044883919173783351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101369909453023784463422269 38013716044883919173783351)
    ·
      refine ⟨57020574067325878760675027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38013716044883919173783351 57020574067325878760675027)
      ·
        refine ⟨85530861100988818141012541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57020574067325878760675027 85530861100988818141012541)
        ·
          refine ⟨32074072912870806802879703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85530861100988818141012541 32074072912870806802879703)
          ·
            refine ⟨48111109369306210204319555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32074072912870806802879703 48111109369306210204319555)
            ·
              refine ⟨72166664053959315306479333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48111109369306210204319555 72166664053959315306479333)
              ·
                refine ⟨13531249510117371619964875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72166664053959315306479333 13531249510117371619964875)
                ·
                  refine ⟨20296874265176057429947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13531249510117371619964875 20296874265176057429947313)
                  ·
                    refine ⟨15222655698882043072460485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20296874265176057429947313 15222655698882043072460485)
                    ·
                      refine ⟨2854247943540383076086341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15222655698882043072460485 2854247943540383076086341)
                      ·
                        rfl

theorem cell23_5558628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_5558628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558628 prefixEnd_5558628 := by exact prefixLift 5558628
  have htrace : WordTrace (prefixWord ++ tailWord_5558628) baseStart_5558628 baseEnd_5558628 := by
    simpa [prefixWord, tailWord_5558628, baseEnd_5558628] using wordTrace_append hprefix tailTrace_5558628
  have hstable : (prefixWord ++ tailWord_5558628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558628).length < 2 ^ (prefixWord ++ tailWord_5558628).sum := by decide
  have hdescent : baseEnd_5558628 < baseStart_5558628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558632 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5558632 : Nat := 118140960795 + 5558632 * 2 ^ 59
def prefixEnd_5558632 : Nat := 4983230072969 + 3 ^ 40 * 5558632 * 2
def baseEnd_5558632 : Nat := 2854249997463001060436323

theorem tailTrace_5558632 : CollatzResearch.WordTrace tailWord_5558632 prefixEnd_5558632 2854249997463001060436323 := by
  unfold tailWord_5558632
  simp only [CollatzResearch.WordTrace]
  refine ⟨101369982399016538804995075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135159976532022051739993433 101369982399016538804995075)
  ·
    refine ⟨152054973598524808207492613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101369982399016538804995075 152054973598524808207492613)
    ·
      refine ⟨28510307549723401538904865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152054973598524808207492613 28510307549723401538904865)
      ·
        refine ⟨21382730662292551154178649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28510307549723401538904865 21382730662292551154178649)
        ·
          refine ⟨16037047996719413365633987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21382730662292551154178649 16037047996719413365633987)
          ·
            refine ⟨24055571995079120048450981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037047996719413365633987 24055571995079120048450981)
            ·
              refine ⟨4510419749077335009084559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24055571995079120048450981 4510419749077335009084559)
              ·
                refine ⟨6765629623616002513626839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510419749077335009084559 6765629623616002513626839)
                ·
                  refine ⟨10148444435424003770440259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765629623616002513626839 10148444435424003770440259)
                  ·
                    refine ⟨15222666653136005655660389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10148444435424003770440259 15222666653136005655660389)
                    ·
                      refine ⟨2854249997463001060436323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15222666653136005655660389 2854249997463001060436323)
                      ·
                        rfl

theorem cell23_5558632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5558632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558632 prefixEnd_5558632 := by exact prefixLift 5558632
  have htrace : WordTrace (prefixWord ++ tailWord_5558632) baseStart_5558632 baseEnd_5558632 := by
    simpa [prefixWord, tailWord_5558632, baseEnd_5558632] using wordTrace_append hprefix tailTrace_5558632
  have hstable : (prefixWord ++ tailWord_5558632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558632).length < 2 ^ (prefixWord ++ tailWord_5558632).sum := by decide
  have hdescent : baseEnd_5558632 < baseStart_5558632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558641 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_5558641 : Nat := 118140960795 + 5558641 * 2 ^ 59
def prefixEnd_5558641 : Nat := 4983230072969 + 3 ^ 40 * 5558641 * 2
def baseEnd_5558641 : Nat := 2854254618788891525223781

theorem tailTrace_5558641 : CollatzResearch.WordTrace tailWord_5558641 prefixEnd_5558641 2854254618788891525223781 := by
  unfold tailWord_5558641
  simp only [CollatzResearch.WordTrace]
  refine ⟨202740293055000472147067777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135160195370000314764711851 202740293055000472147067777)
  ·
    refine ⟨152055219791250354110300833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202740293055000472147067777 152055219791250354110300833)
    ·
      refine ⟨114041414843437765582725625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152055219791250354110300833 114041414843437765582725625)
      ·
        refine ⟨85531061132578324187044219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114041414843437765582725625 85531061132578324187044219)
        ·
          refine ⟨128296591698867486280566329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85531061132578324187044219 128296591698867486280566329)
          ·
            refine ⟨96222443774150614710424747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128296591698867486280566329 96222443774150614710424747)
            ·
              refine ⟨144333665661225922065637121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96222443774150614710424747 144333665661225922065637121)
              ·
                refine ⟨108250249245919441549227841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144333665661225922065637121 108250249245919441549227841)
                ·
                  refine ⟨81187686934439581161920881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108250249245919441549227841 81187686934439581161920881)
                  ·
                    refine ⟨60890765200829685871440661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81187686934439581161920881 60890765200829685871440661)
                    ·
                      refine ⟨2854254618788891525223781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60890765200829685871440661 2854254618788891525223781)
                      ·
                        rfl

theorem cell23_5558641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_5558641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558641 prefixEnd_5558641 := by exact prefixLift 5558641
  have htrace : WordTrace (prefixWord ++ tailWord_5558641) baseStart_5558641 baseEnd_5558641 := by
    simpa [prefixWord, tailWord_5558641, baseEnd_5558641] using wordTrace_append hprefix tailTrace_5558641
  have hstable : (prefixWord ++ tailWord_5558641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558641).length < 2 ^ (prefixWord ++ tailWord_5558641).sum := by decide
  have hdescent : baseEnd_5558641 < baseStart_5558641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558642 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_5558642 : Nat := 118140960795 + 5558642 * 2 ^ 59
def prefixEnd_5558642 : Nat := 4983230072969 + 3 ^ 40 * 5558642 * 2
def baseEnd_5558642 : Nat := 951418377423182007103759

theorem tailTrace_5558642 : CollatzResearch.WordTrace tailWord_5558642 prefixEnd_5558642 951418377423182007103759 := by
  unfold tailWord_5558642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50685082381999212329463545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135160219685331232878569453 50685082381999212329463545)
  ·
    refine ⟨38013811786499409247097659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50685082381999212329463545 38013811786499409247097659)
    ·
      refine ⟨57020717679749113870646489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38013811786499409247097659 57020717679749113870646489)
      ·
        refine ⟨42765538259811835402984867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57020717679749113870646489 42765538259811835402984867)
        ·
          refine ⟨64148307389717753104477301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42765538259811835402984867 64148307389717753104477301)
          ·
            refine ⟨6013903817786039353544747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64148307389717753104477301 6013903817786039353544747)
            ·
              refine ⟨9020855726679059030317121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013903817786039353544747 9020855726679059030317121)
              ·
                refine ⟨6765641795009294272737841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020855726679059030317121 6765641795009294272737841)
                ·
                  refine ⟨5074231346256970704553381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765641795009294272737841 5074231346256970704553381)
                  ·
                    refine ⟨951418377423182007103759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074231346256970704553381 951418377423182007103759)
                    ·
                      rfl

theorem cell23_5558642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_5558642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558642 prefixEnd_5558642 := by exact prefixLift 5558642
  have htrace : WordTrace (prefixWord ++ tailWord_5558642) baseStart_5558642 baseEnd_5558642 := by
    simpa [prefixWord, tailWord_5558642, baseEnd_5558642] using wordTrace_append hprefix tailTrace_5558642
  have hstable : (prefixWord ++ tailWord_5558642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558642).length < 2 ^ (prefixWord ++ tailWord_5558642).sum := by decide
  have hdescent : baseEnd_5558642 < baseStart_5558642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558665 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_5558665 : Nat := 118140960795 + 5558665 * 2 ^ 59
def prefixEnd_5558665 : Nat := 4983230072969 + 3 ^ 40 * 5558665 * 2
def baseEnd_5558665 : Nat := 2854266942324599431323671

theorem tailTrace_5558665 : CollatzResearch.WordTrace tailWord_5558665 prefixEnd_5558665 2854266942324599431323671 := by
  unfold tailWord_5558665
  simp only [CollatzResearch.WordTrace]
  refine ⟨202741168406913524245941449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135160778937942349497294299 202741168406913524245941449)
  ·
    refine ⟨152055876305185143184456087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202741168406913524245941449 152055876305185143184456087)
    ·
      refine ⟨228083814457777714776684131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152055876305185143184456087 228083814457777714776684131)
      ·
        refine ⟨342125721686666572165026197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228083814457777714776684131 342125721686666572165026197)
        ·
          refine ⟨16037143204062495570235603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 342125721686666572165026197 16037143204062495570235603)
          ·
            refine ⟨24055714806093743355353405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037143204062495570235603 24055714806093743355353405)
            ·
              refine ⟨9020893052285153758257527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24055714806093743355353405 9020893052285153758257527)
              ·
                refine ⟨13531339578427730637386291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9020893052285153758257527 13531339578427730637386291)
                ·
                  refine ⟨20297009367641595956079437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13531339578427730637386291 20297009367641595956079437)
                  ·
                    refine ⟨7611378512865598483529789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20297009367641595956079437 7611378512865598483529789)
                    ·
                      refine ⟨2854266942324599431323671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611378512865598483529789 2854266942324599431323671)
                      ·
                        rfl

theorem cell23_5558665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_5558665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558665 prefixEnd_5558665 := by exact prefixLift 5558665
  have htrace : WordTrace (prefixWord ++ tailWord_5558665) baseStart_5558665 baseEnd_5558665 := by
    simpa [prefixWord, tailWord_5558665, baseEnd_5558665] using wordTrace_append hprefix tailTrace_5558665
  have hstable : (prefixWord ++ tailWord_5558665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558665).length < 2 ^ (prefixWord ++ tailWord_5558665).sum := by decide
  have hdescent : baseEnd_5558665 < baseStart_5558665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558692 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_5558692 : Nat := 118140960795 + 5558692 * 2 ^ 59
def prefixEnd_5558692 : Nat := 4983230072969 + 3 ^ 40 * 5558692 * 2
def baseEnd_5558692 : Nat := 2854280806302270825686047

theorem tailTrace_5558692 : CollatzResearch.WordTrace tailWord_5558692 prefixEnd_5558692 2854280806302270825686047 := by
  unfold tailWord_5558692
  simp only [CollatzResearch.WordTrace]
  refine ⟨101371076588907853928587165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135161435451877138571449553 101371076588907853928587165)
  ·
    refine ⟨38014153720840445223220187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101371076588907853928587165 38014153720840445223220187)
    ·
      refine ⟨57021230581260667834830281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38014153720840445223220187 57021230581260667834830281)
      ·
        refine ⟨42765922935945500876122711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57021230581260667834830281 42765922935945500876122711)
        ·
          refine ⟨64148884403918251314184067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42765922935945500876122711 64148884403918251314184067)
          ·
            refine ⟨96223326605877376971276101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64148884403918251314184067 96223326605877376971276101)
            ·
              refine ⟨18041873738602008182114269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96223326605877376971276101 18041873738602008182114269)
              ·
                refine ⟨6765702651975753068292851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18041873738602008182114269 6765702651975753068292851)
                ·
                  refine ⟨10148553977963629602439277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765702651975753068292851 10148553977963629602439277)
                  ·
                    refine ⟨3805707741736361100914729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10148553977963629602439277 3805707741736361100914729)
                    ·
                      refine ⟨2854280806302270825686047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805707741736361100914729 2854280806302270825686047)
                      ·
                        rfl

theorem cell23_5558692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_5558692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558692 prefixEnd_5558692 := by exact prefixLift 5558692
  have htrace : WordTrace (prefixWord ++ tailWord_5558692) baseStart_5558692 baseEnd_5558692 := by
    simpa [prefixWord, tailWord_5558692, baseEnd_5558692] using wordTrace_append hprefix tailTrace_5558692
  have hstable : (prefixWord ++ tailWord_5558692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558692).length < 2 ^ (prefixWord ++ tailWord_5558692).sum := by decide
  have hdescent : baseEnd_5558692 < baseStart_5558692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558716 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5558716 : Nat := 118140960795 + 5558716 * 2 ^ 59
def prefixEnd_5558716 : Nat := 4983230072969 + 3 ^ 40 * 5558716 * 2
def baseEnd_5558716 : Nat := 2854293129837978731785937

theorem tailTrace_5558716 : CollatzResearch.WordTrace tailWord_5558716 prefixEnd_5558716 2854293129837978731785937 := by
  unfold tailWord_5558716
  simp only [CollatzResearch.WordTrace]
  refine ⟨101371514264864379978024001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135162019019819173304032001 101371514264864379978024001)
  ·
    refine ⟨76028635698648284983518001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101371514264864379978024001 76028635698648284983518001)
    ·
      refine ⟨57021476773986213737638501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76028635698648284983518001 57021476773986213737638501)
      ·
        refine ⟨10691526895122415075807219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57021476773986213737638501 10691526895122415075807219)
        ·
          refine ⟨16037290342683622613710829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691526895122415075807219 16037290342683622613710829)
          ·
            refine ⟨6013983878506358480141561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16037290342683622613710829 6013983878506358480141561)
            ·
              refine ⟨4510487908879768860106171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6013983878506358480141561 4510487908879768860106171)
              ·
                refine ⟨6765731863319653290159257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510487908879768860106171 6765731863319653290159257)
                ·
                  refine ⟨5074298897489739967619443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765731863319653290159257 5074298897489739967619443)
                  ·
                    refine ⟨7611448346234609951429165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074298897489739967619443 7611448346234609951429165)
                    ·
                      refine ⟨2854293129837978731785937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611448346234609951429165 2854293129837978731785937)
                      ·
                        rfl

theorem cell23_5558716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5558716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558716 prefixEnd_5558716 := by exact prefixLift 5558716
  have htrace : WordTrace (prefixWord ++ tailWord_5558716) baseStart_5558716 baseEnd_5558716 := by
    simpa [prefixWord, tailWord_5558716, baseEnd_5558716] using wordTrace_append hprefix tailTrace_5558716
  have hstable : (prefixWord ++ tailWord_5558716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558716).length < 2 ^ (prefixWord ++ tailWord_5558716).sum := by decide
  have hdescent : baseEnd_5558716 < baseStart_5558716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558745 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 5]
def baseStart_5558745 : Nat := 118140960795 + 5558745 * 2 ^ 59
def prefixEnd_5558745 : Nat := 4983230072969 + 3 ^ 40 * 5558745 * 2
def baseEnd_5558745 : Nat := 317145335641884346480367

theorem tailTrace_5558745 : CollatzResearch.WordTrace tailWord_5558745 prefixEnd_5558745 317145335641884346480367 := by
  unfold tailWord_5558745
  simp only [CollatzResearch.WordTrace]
  refine ⟨202744086246623697908853689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135162724164415798605902459 202744086246623697908853689)
  ·
    refine ⟨152058064684967773431640267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202744086246623697908853689 152058064684967773431640267)
    ·
      refine ⟨228087097027451660147460401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152058064684967773431640267 228087097027451660147460401)
      ·
        refine ⟨171065322770588745110595301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228087097027451660147460401 171065322770588745110595301)
        ·
          refine ⟨32074748019485389708236619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171065322770588745110595301 32074748019485389708236619)
          ·
            refine ⟨48112122029228084562354929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32074748019485389708236619 48112122029228084562354929)
            ·
              refine ⟨36084091521921063421766197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48112122029228084562354929 36084091521921063421766197)
              ·
                refine ⟨3382883580180099695790581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36084091521921063421766197 3382883580180099695790581)
                ·
                  refine ⟨317145335641884346480367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382883580180099695790581 317145335641884346480367)
                  ·
                    rfl

theorem cell23_5558745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 5].length) (baseStart_5558745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558745 prefixEnd_5558745 := by exact prefixLift 5558745
  have htrace : WordTrace (prefixWord ++ tailWord_5558745) baseStart_5558745 baseEnd_5558745 := by
    simpa [prefixWord, tailWord_5558745, baseEnd_5558745] using wordTrace_append hprefix tailTrace_5558745
  have hstable : (prefixWord ++ tailWord_5558745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558745).length < 2 ^ (prefixWord ++ tailWord_5558745).sum := by decide
  have hdescent : baseEnd_5558745 < baseStart_5558745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558762 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_5558762 : Nat := 118140960795 + 5558762 * 2 ^ 59
def prefixEnd_5558762 : Nat := 4983230072969 + 3 ^ 40 * 5558762 * 2
def baseEnd_5558762 : Nat := 317146305549787283534525

theorem tailTrace_5558762 : CollatzResearch.WordTrace tailWord_5558762 prefixEnd_5558762 317146305549787283534525 := by
  unfold tailWord_5558762
  simp only [CollatzResearch.WordTrace]
  refine ⟨50686176571890527453055635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135163137525041406541481693 50686176571890527453055635)
  ·
    refine ⟨76029264857835791179583453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50686176571890527453055635 76029264857835791179583453)
    ·
      refine ⟨28510974321688421692343795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76029264857835791179583453 28510974321688421692343795)
      ·
        refine ⟨42766461482532632538515693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28510974321688421692343795 42766461482532632538515693)
        ·
          refine ⟨16037423055949737201943385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42766461482532632538515693 16037423055949737201943385)
          ·
            refine ⟨12028067291962302901457539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16037423055949737201943385 12028067291962302901457539)
            ·
              refine ⟨18042100937943454352186309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12028067291962302901457539 18042100937943454352186309)
              ·
                refine ⟨3382893925864397691034933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18042100937943454352186309 3382893925864397691034933)
                ·
                  refine ⟨317146305549787283534525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382893925864397691034933 317146305549787283534525)
                  ·
                    rfl

theorem cell23_5558762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_5558762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558762 prefixEnd_5558762 := by exact prefixLift 5558762
  have htrace : WordTrace (prefixWord ++ tailWord_5558762) baseStart_5558762 baseEnd_5558762 := by
    simpa [prefixWord, tailWord_5558762, baseEnd_5558762] using wordTrace_append hprefix tailTrace_5558762
  have hstable : (prefixWord ++ tailWord_5558762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558762).length < 2 ^ (prefixWord ++ tailWord_5558762).sum := by decide
  have hdescent : baseEnd_5558762 < baseStart_5558762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558768 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_5558768 : Nat := 118140960795 + 5558768 * 2 ^ 59
def prefixEnd_5558768 : Nat := 4983230072969 + 3 ^ 40 * 5558768 * 2
def baseEnd_5558768 : Nat := 2854319830832012528335697

theorem tailTrace_5558768 : CollatzResearch.WordTrace tailWord_5558768 prefixEnd_5558768 2854319830832012528335697 := by
  unfold tailWord_5558768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101372462562770186418470479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135163283417026915224627305 101372462562770186418470479)
  ·
    refine ⟨152058693844155279627705719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101372462562770186418470479 152058693844155279627705719)
    ·
      refine ⟨228088040766232919441558579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152058693844155279627705719 228088040766232919441558579)
      ·
        refine ⟨342132061149349379162337869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228088040766232919441558579 342132061149349379162337869)
        ·
          refine ⟨128299522931006017185876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342132061149349379162337869 128299522931006017185876701)
          ·
            refine ⟨48112321099127256444703763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128299522931006017185876701 48112321099127256444703763)
            ·
              refine ⟨72168481648690884667055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48112321099127256444703763 72168481648690884667055645)
              ·
                refine ⟨27063180618259081750145867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72168481648690884667055645 27063180618259081750145867)
                ·
                  refine ⟨40594770927388622625218801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27063180618259081750145867 40594770927388622625218801)
                  ·
                    refine ⟨30446078195541466968914101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40594770927388622625218801 30446078195541466968914101)
                    ·
                      refine ⟨2854319830832012528335697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30446078195541466968914101 2854319830832012528335697)
                      ·
                        rfl

theorem cell23_5558768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_5558768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558768 prefixEnd_5558768 := by exact prefixLift 5558768
  have htrace : WordTrace (prefixWord ++ tailWord_5558768) baseStart_5558768 baseEnd_5558768 := by
    simpa [prefixWord, tailWord_5558768, baseEnd_5558768] using wordTrace_append hprefix tailTrace_5558768
  have hstable : (prefixWord ++ tailWord_5558768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558768).length < 2 ^ (prefixWord ++ tailWord_5558768).sum := by decide
  have hdescent : baseEnd_5558768 < baseStart_5558768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558795 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_5558795 : Nat := 118140960795 + 5558795 * 2 ^ 59
def prefixEnd_5558795 : Nat := 4983230072969 + 3 ^ 40 * 5558795 * 2
def baseEnd_5558795 : Nat := 2854333694809683922698073

theorem tailTrace_5558795 : CollatzResearch.WordTrace tailWord_5558795 prefixEnd_5558795 2854333694809683922698073 := by
  unfold tailWord_5558795
  simp only [CollatzResearch.WordTrace]
  refine ⟨202745909896442556448173839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135163939930961704298782559 202745909896442556448173839)
  ·
    refine ⟨304118864844663834672260759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202745909896442556448173839 304118864844663834672260759)
    ·
      refine ⟨456178297266995752008391139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304118864844663834672260759 456178297266995752008391139)
      ·
        refine ⟨684267445900493628012586709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456178297266995752008391139 684267445900493628012586709)
        ·
          refine ⟨16037518263292819406545001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 684267445900493628012586709 16037518263292819406545001)
          ·
            refine ⟨12028138697469614554908751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16037518263292819406545001 12028138697469614554908751)
            ·
              refine ⟨18042208046204421832363127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12028138697469614554908751 18042208046204421832363127)
              ·
                refine ⟨27063312069306632748544691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18042208046204421832363127 27063312069306632748544691)
                ·
                  refine ⟨40594968103959949122817037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27063312069306632748544691 40594968103959949122817037)
                  ·
                    refine ⟨15223113038984980921056389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40594968103959949122817037 15223113038984980921056389)
                    ·
                      refine ⟨2854333694809683922698073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15223113038984980921056389 2854333694809683922698073)
                      ·
                        rfl

theorem cell23_5558795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_5558795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558795 prefixEnd_5558795 := by exact prefixLift 5558795
  have htrace : WordTrace (prefixWord ++ tailWord_5558795) baseStart_5558795 baseEnd_5558795 := by
    simpa [prefixWord, tailWord_5558795, baseEnd_5558795] using wordTrace_append hprefix tailTrace_5558795
  have hstable : (prefixWord ++ tailWord_5558795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558795).length < 2 ^ (prefixWord ++ tailWord_5558795).sum := by decide
  have hdescent : baseEnd_5558795 < baseStart_5558795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558805 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5558805 : Nat := 118140960795 + 5558805 * 2 ^ 59
def prefixEnd_5558805 : Nat := 4983230072969 + 3 ^ 40 * 5558805 * 2
def baseEnd_5558805 : Nat := 951446276538742961191009

theorem tailTrace_5558805 : CollatzResearch.WordTrace tailWord_5558805 prefixEnd_5558805 951446276538742961191009 := by
  unfold tailWord_5558805
  simp only [CollatzResearch.WordTrace]
  refine ⟨202746274626406328156037869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135164183084270885437358579 202746274626406328156037869)
  ·
    refine ⟨76029852984902373058514201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202746274626406328156037869 76029852984902373058514201)
    ·
      refine ⟨57022389738676779793885651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76029852984902373058514201 57022389738676779793885651)
      ·
        refine ⟨85533584608015169690828477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57022389738676779793885651 85533584608015169690828477)
        ·
          refine ⟨32075094228005688634060679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85533584608015169690828477 32075094228005688634060679)
          ·
            refine ⟨48112641342008532951091019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32075094228005688634060679 48112641342008532951091019)
            ·
              refine ⟨72168962013012799426636529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48112641342008532951091019 72168962013012799426636529)
              ·
                refine ⟨54126721509759599569977397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72168962013012799426636529 54126721509759599569977397)
                ·
                  refine ⟨5074380141539962459685381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54126721509759599569977397 5074380141539962459685381)
                  ·
                    refine ⟨951446276538742961191009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074380141539962459685381 951446276538742961191009)
                    ·
                      rfl

theorem cell23_5558805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5558805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558805 prefixEnd_5558805 := by exact prefixLift 5558805
  have htrace : WordTrace (prefixWord ++ tailWord_5558805) baseStart_5558805 baseEnd_5558805 := by
    simpa [prefixWord, tailWord_5558805, baseEnd_5558805] using wordTrace_append hprefix tailTrace_5558805
  have hstable : (prefixWord ++ tailWord_5558805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558805).length < 2 ^ (prefixWord ++ tailWord_5558805).sum := by decide
  have hdescent : baseEnd_5558805 < baseStart_5558805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558812 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_5558812 : Nat := 118140960795 + 5558812 * 2 ^ 59
def prefixEnd_5558812 : Nat := 4983230072969 + 3 ^ 40 * 5558812 * 2
def baseEnd_5558812 : Nat := 2854342423980810356185495

theorem tailTrace_5558812 : CollatzResearch.WordTrace tailWord_5558812 prefixEnd_5558812 2854342423980810356185495 := by
  unfold tailWord_5558812
  simp only [CollatzResearch.WordTrace]
  refine ⟨101373264968690484175771345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135164353291587312234361793 101373264968690484175771345)
  ·
    refine ⟨76029948726517863131828509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101373264968690484175771345 76029948726517863131828509)
    ·
      refine ⟨28511230772444198674435691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76029948726517863131828509 28511230772444198674435691)
      ·
        refine ⟨42766846158666298011653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28511230772444198674435691 42766846158666298011653537)
        ·
          refine ⟨32075134618999723508740153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42766846158666298011653537 32075134618999723508740153)
          ·
            refine ⟨24056350964249792631555115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32075134618999723508740153 24056350964249792631555115)
            ·
              refine ⟨36084526446374688947332673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24056350964249792631555115 36084526446374688947332673)
              ·
                refine ⟨27063394834781016710499505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36084526446374688947332673 27063394834781016710499505)
                ·
                  refine ⟨20297546126085762532874629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27063394834781016710499505 20297546126085762532874629)
                  ·
                    refine ⟨3805789898641080474913993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20297546126085762532874629 3805789898641080474913993)
                    ·
                      refine ⟨2854342423980810356185495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805789898641080474913993 2854342423980810356185495)
                      ·
                        rfl

theorem cell23_5558812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_5558812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558812 prefixEnd_5558812 := by exact prefixLift 5558812
  have htrace : WordTrace (prefixWord ++ tailWord_5558812) baseStart_5558812 baseEnd_5558812 := by
    simpa [prefixWord, tailWord_5558812, baseEnd_5558812] using wordTrace_append hprefix tailTrace_5558812
  have hstable : (prefixWord ++ tailWord_5558812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558812).length < 2 ^ (prefixWord ++ tailWord_5558812).sum := by decide
  have hdescent : baseEnd_5558812 < baseStart_5558812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558815 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_5558815 : Nat := 118140960795 + 5558815 * 2 ^ 59
def prefixEnd_5558815 : Nat := 4983230072969 + 3 ^ 40 * 5558815 * 2
def baseEnd_5558815 : Nat := 2854343964422773844447981

theorem tailTrace_5558815 : CollatzResearch.WordTrace tailWord_5558815 prefixEnd_5558815 2854343964422773844447981 := by
  unfold tailWord_5558815
  simp only [CollatzResearch.WordTrace]
  refine ⟨202746639356370099863901899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135164426237580066575934599 202746639356370099863901899)
  ·
    refine ⟨304119959034555149795852849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202746639356370099863901899 304119959034555149795852849)
    ·
      refine ⟨228089969275916362346889637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304119959034555149795852849 228089969275916362346889637)
      ·
        refine ⟨42766869239234317940041807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228089969275916362346889637 42766869239234317940041807)
        ·
          refine ⟨64150303858851476910062711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42766869239234317940041807 64150303858851476910062711)
          ·
            refine ⟨96225455788277215365094067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64150303858851476910062711 96225455788277215365094067)
            ·
              refine ⟨144338183682415823047641101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96225455788277215365094067 144338183682415823047641101)
              ·
                refine ⟨54126818880905933642865413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144338183682415823047641101 54126818880905933642865413)
                ·
                  refine ⟨10148778540169862558037265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54126818880905933642865413 10148778540169862558037265)
                  ·
                    refine ⟨7611583905127396918527949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10148778540169862558037265 7611583905127396918527949)
                    ·
                      refine ⟨2854343964422773844447981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611583905127396918527949 2854343964422773844447981)
                      ·
                        rfl

theorem cell23_5558815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_5558815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558815 prefixEnd_5558815 := by exact prefixLift 5558815
  have htrace : WordTrace (prefixWord ++ tailWord_5558815) baseStart_5558815 baseEnd_5558815 := by
    simpa [prefixWord, tailWord_5558815, baseEnd_5558815] using wordTrace_append hprefix tailTrace_5558815
  have hstable : (prefixWord ++ tailWord_5558815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558815).length < 2 ^ (prefixWord ++ tailWord_5558815).sum := by decide
  have hdescent : baseEnd_5558815 < baseStart_5558815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558862 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_5558862 : Nat := 118140960795 + 5558862 * 2 ^ 59
def prefixEnd_5558862 : Nat := 4983230072969 + 3 ^ 40 * 5558862 * 2
def baseEnd_5558862 : Nat := 2854368098013535160560265

theorem tailTrace_5558862 : CollatzResearch.WordTrace tailWord_5558862 prefixEnd_5558862 2854368098013535160560265 := by
  unfold tailWord_5558862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25343544198399978361357855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135165569058133217927241893 25343544198399978361357855)
  ·
    refine ⟨38015316297599967542036783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25343544198399978361357855 38015316297599967542036783)
    ·
      refine ⟨57022974446399951313055175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38015316297599967542036783 57022974446399951313055175)
      ·
        refine ⟨85534461669599926969582763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57022974446399951313055175 85534461669599926969582763)
        ·
          refine ⟨128301692504399890454374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85534461669599926969582763 128301692504399890454374145)
          ·
            refine ⟨96226269378299917840780609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128301692504399890454374145 96226269378299917840780609)
            ·
              refine ⟨72169702033724938380585457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96226269378299917840780609 72169702033724938380585457)
              ·
                refine ⟨54127276525293703785439093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72169702033724938380585457 54127276525293703785439093)
                ·
                  refine ⟨5074432174246284729884915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54127276525293703785439093 5074432174246284729884915)
                  ·
                    refine ⟨7611648261369427094827373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074432174246284729884915 7611648261369427094827373)
                    ·
                      refine ⟨2854368098013535160560265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611648261369427094827373 2854368098013535160560265)
                      ·
                        rfl

theorem cell23_5558862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_5558862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558862 prefixEnd_5558862 := by exact prefixLift 5558862
  have htrace : WordTrace (prefixWord ++ tailWord_5558862) baseStart_5558862 baseEnd_5558862 := by
    simpa [prefixWord, tailWord_5558862, baseEnd_5558862] using wordTrace_append hprefix tailTrace_5558862
  have hstable : (prefixWord ++ tailWord_5558862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558862).length < 2 ^ (prefixWord ++ tailWord_5558862).sum := by decide
  have hdescent : baseEnd_5558862 < baseStart_5558862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558872 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_5558872 : Nat := 118140960795 + 5558872 * 2 ^ 59
def prefixEnd_5558872 : Nat := 4983230072969 + 3 ^ 40 * 5558872 * 2
def baseEnd_5558872 : Nat := 2854373232820080121435219

theorem tailTrace_5558872 : CollatzResearch.WordTrace tailWord_5558872 prefixEnd_5558872 2854373232820080121435219 := by
  unfold tailWord_5558872
  simp only [CollatzResearch.WordTrace]
  refine ⟨101374359158581799299363435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135165812211442399065817913 101374359158581799299363435)
  ·
    refine ⟨152061538737872698949045153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101374359158581799299363435 152061538737872698949045153)
    ·
      refine ⟨114046154053404524211783865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152061538737872698949045153 114046154053404524211783865)
      ·
        refine ⟨85534615540053393158837899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114046154053404524211783865 85534615540053393158837899)
        ·
          refine ⟨128301923310080089738256849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85534615540053393158837899 128301923310080089738256849)
          ·
            refine ⟨96226442482560067303692637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128301923310080089738256849 96226442482560067303692637)
            ·
              refine ⟨36084915930960025238884739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96226442482560067303692637 36084915930960025238884739)
              ·
                refine ⟨54127373896440037858327109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36084915930960025238884739 54127373896440037858327109)
                ·
                  refine ⟨10148882605582507098436333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54127373896440037858327109 10148882605582507098436333)
                  ·
                    refine ⟨3805830977093440161913625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10148882605582507098436333 3805830977093440161913625)
                    ·
                      refine ⟨2854373232820080121435219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805830977093440161913625 2854373232820080121435219)
                      ·
                        rfl

theorem cell23_5558872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_5558872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558872 prefixEnd_5558872 := by exact prefixLift 5558872
  have htrace : WordTrace (prefixWord ++ tailWord_5558872) baseStart_5558872 baseEnd_5558872 := by
    simpa [prefixWord, tailWord_5558872, baseEnd_5558872] using wordTrace_append hprefix tailTrace_5558872
  have hstable : (prefixWord ++ tailWord_5558872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558872).length < 2 ^ (prefixWord ++ tailWord_5558872).sum := by decide
  have hdescent : baseEnd_5558872 < baseStart_5558872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 1, 1, 3]
def baseStart_5558879 : Nat := 118140960795 + 5558879 * 2 ^ 59
def prefixEnd_5558879 : Nat := 4983230072969 + 3 ^ 40 * 5558879 * 2
def baseEnd_5558879 : Nat := 2854376827184661594047687

theorem tailTrace_5558879 : CollatzResearch.WordTrace tailWord_5558879 prefixEnd_5558879 2854376827184661594047687 := by
  unfold tailWord_5558879
  simp only [CollatzResearch.WordTrace]
  refine ⟨202748973628138238794231691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135165982418758825862821127 202748973628138238794231691)
  ·
    refine ⟨304123460442207358191347537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202748973628138238794231691 304123460442207358191347537)
    ·
      refine ⟨228092595331655518643510653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304123460442207358191347537 228092595331655518643510653)
      ·
        refine ⟨85534723249370819491316495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228092595331655518643510653 85534723249370819491316495)
        ·
          refine ⟨128302084874056229236974743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85534723249370819491316495 128302084874056229236974743)
          ·
            refine ⟨192453127311084343855462115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128302084874056229236974743 192453127311084343855462115)
            ·
              refine ⟨288679690966626515783193173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192453127311084343855462115 288679690966626515783193173)
              ·
                refine ⟨3382965128515154481834295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 288679690966626515783193173 3382965128515154481834295)
                ·
                  refine ⟨5074447692772731722751443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382965128515154481834295 5074447692772731722751443)
                  ·
                    refine ⟨7611671539159097584127165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074447692772731722751443 7611671539159097584127165)
                    ·
                      refine ⟨2854376827184661594047687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611671539159097584127165 2854376827184661594047687)
                      ·
                        rfl

theorem cell23_5558879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_5558879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558879 prefixEnd_5558879 := by exact prefixLift 5558879
  have htrace : WordTrace (prefixWord ++ tailWord_5558879) baseStart_5558879 baseEnd_5558879 := by
    simpa [prefixWord, tailWord_5558879, baseEnd_5558879] using wordTrace_append hprefix tailTrace_5558879
  have hstable : (prefixWord ++ tailWord_5558879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558879).length < 2 ^ (prefixWord ++ tailWord_5558879).sum := by decide
  have hdescent : baseEnd_5558879 < baseStart_5558879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558915 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_5558915 : Nat := 118140960795 + 5558915 * 2 ^ 59
def prefixEnd_5558915 : Nat := 4983230072969 + 3 ^ 40 * 5558915 * 2
def baseEnd_5558915 : Nat := 2854395312488223453197521

theorem tailTrace_5558915 : CollatzResearch.WordTrace tailWord_5558915 prefixEnd_5558915 2854395312488223453197521 := by
  unfold tailWord_5558915
  simp only [CollatzResearch.WordTrace]
  refine ⟨202750286656007816942542199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135166857770671877961694799 202750286656007816942542199)
  ·
    refine ⟨304125429984011725413813299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202750286656007816942542199 304125429984011725413813299)
    ·
      refine ⟨456188144976017588120719949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304125429984011725413813299 456188144976017588120719949)
      ·
        refine ⟨171070554366006595545269981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456188144976017588120719949 171070554366006595545269981)
        ·
          refine ⟨64151457887252473329476243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171070554366006595545269981 64151457887252473329476243)
          ·
            refine ⟨96227186830878709994214365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64151457887252473329476243 96227186830878709994214365)
            ·
              refine ⟨36085195061579516247830387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96227186830878709994214365 36085195061579516247830387)
              ·
                refine ⟨54127792592369274371745581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36085195061579516247830387 54127792592369274371745581)
                ·
                  refine ⟨20297922222138477889404593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54127792592369274371745581 20297922222138477889404593)
                  ·
                    refine ⟨15223441666603858417053445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20297922222138477889404593 15223441666603858417053445)
                    ·
                      refine ⟨2854395312488223453197521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15223441666603858417053445 2854395312488223453197521)
                      ·
                        rfl

theorem cell23_5558915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_5558915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558915 prefixEnd_5558915 := by exact prefixLift 5558915
  have htrace : WordTrace (prefixWord ++ tailWord_5558915) baseStart_5558915 baseEnd_5558915 := by
    simpa [prefixWord, tailWord_5558915, baseEnd_5558915] using wordTrace_append hprefix tailTrace_5558915
  have hstable : (prefixWord ++ tailWord_5558915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558915).length < 2 ^ (prefixWord ++ tailWord_5558915).sum := by decide
  have hdescent : baseEnd_5558915 < baseStart_5558915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558919 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_5558919 : Nat := 118140960795 + 5558919 * 2 ^ 59
def prefixEnd_5558919 : Nat := 4983230072969 + 3 ^ 40 * 5558919 * 2
def baseEnd_5558919 : Nat := 2854397366410841437547503

theorem tailTrace_5558919 : CollatzResearch.WordTrace tailWord_5558919 prefixEnd_5558919 2854397366410841437547503 := by
  unfold tailWord_5558919
  simp only [CollatzResearch.WordTrace]
  refine ⟨202750432547993325625687811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135166955031995550417125207 202750432547993325625687811)
  ·
    refine ⟨304125648821989988438531717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202750432547993325625687811 304125648821989988438531717)
    ·
      refine ⟨57023559154123122832224697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304125648821989988438531717 57023559154123122832224697)
      ·
        refine ⟨42767669365592342124168523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57023559154123122832224697 42767669365592342124168523)
        ·
          refine ⟨64151504048388513186252785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42767669365592342124168523 64151504048388513186252785)
          ·
            refine ⟨48113628036291384889689589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64151504048388513186252785 48113628036291384889689589)
            ·
              refine ⟨4510652628402317333408399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48113628036291384889689589 4510652628402317333408399)
              ·
                refine ⟨6765978942603476000112599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510652628402317333408399 6765978942603476000112599)
                ·
                  refine ⟨10148968413905214000168899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765978942603476000112599 10148968413905214000168899)
                  ·
                    refine ⟨15223452620857821000253349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10148968413905214000168899 15223452620857821000253349)
                    ·
                      refine ⟨2854397366410841437547503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15223452620857821000253349 2854397366410841437547503)
                      ·
                        rfl

theorem cell23_5558919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_5558919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558919 prefixEnd_5558919 := by exact prefixLift 5558919
  have htrace : WordTrace (prefixWord ++ tailWord_5558919) baseStart_5558919 baseEnd_5558919 := by
    simpa [prefixWord, tailWord_5558919, baseEnd_5558919] using wordTrace_append hprefix tailTrace_5558919
  have hstable : (prefixWord ++ tailWord_5558919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558919).length < 2 ^ (prefixWord ++ tailWord_5558919).sum := by decide
  have hdescent : baseEnd_5558919 < baseStart_5558919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558930 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5558930 : Nat := 118140960795 + 5558930 * 2 ^ 59
def prefixEnd_5558930 : Nat := 4983230072969 + 3 ^ 40 * 5558930 * 2
def baseEnd_5558930 : Nat := 2854403014698040894509953

theorem tailTrace_5558930 : CollatzResearch.WordTrace tailWord_5558930 prefixEnd_5558930 2854403014698040894509953 := by
  unfold tailWord_5558930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50687708437738368626084561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135167222500635649669558829 50687708437738368626084561)
  ·
    refine ⟨38015781328303776469563421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50687708437738368626084561 38015781328303776469563421)
    ·
      refine ⟨14255917998113916176086283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38015781328303776469563421 14255917998113916176086283)
      ·
        refine ⟨21383876997170874264129425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255917998113916176086283 21383876997170874264129425)
        ·
          refine ⟨16037907747878155698097069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21383876997170874264129425 16037907747878155698097069)
          ·
            refine ⟨6014215405454308386786401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16037907747878155698097069 6014215405454308386786401)
            ·
              refine ⟨4510661554090731290089801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014215405454308386786401 4510661554090731290089801)
              ·
                refine ⟨3382996165568048467567351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510661554090731290089801 3382996165568048467567351)
                ·
                  refine ⟨5074494248352072701351027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382996165568048467567351 5074494248352072701351027)
                  ·
                    refine ⟨7611741372528109052026541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074494248352072701351027 7611741372528109052026541)
                    ·
                      refine ⟨2854403014698040894509953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611741372528109052026541 2854403014698040894509953)
                      ·
                        rfl

theorem cell23_5558930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5558930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558930 prefixEnd_5558930 := by exact prefixLift 5558930
  have htrace : WordTrace (prefixWord ++ tailWord_5558930) baseStart_5558930 baseEnd_5558930 := by
    simpa [prefixWord, tailWord_5558930, baseEnd_5558930] using wordTrace_append hprefix tailTrace_5558930
  have hstable : (prefixWord ++ tailWord_5558930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558930).length < 2 ^ (prefixWord ++ tailWord_5558930).sum := by decide
  have hdescent : baseEnd_5558930 < baseStart_5558930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558986 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_5558986 : Nat := 118140960795 + 5558986 * 2 ^ 59
def prefixEnd_5558986 : Nat := 4983230072969 + 3 ^ 40 * 5558986 * 2
def baseEnd_5558986 : Nat := 2854431769614692675409695

theorem tailTrace_5558986 : CollatzResearch.WordTrace tailWord_5558986 prefixEnd_5558986 2854431769614692675409695 := by
  unfold tailWord_5558986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50688219059687649017094203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135168584159167064045584541 50688219059687649017094203)
  ·
    refine ⟨76032328589531473525641305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50688219059687649017094203 76032328589531473525641305)
    ·
      refine ⟨57024246442148605144230979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76032328589531473525641305 57024246442148605144230979)
      ·
        refine ⟨85536369663222907716346469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57024246442148605144230979 85536369663222907716346469)
        ·
          refine ⟨16038069311854295196814963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85536369663222907716346469 16038069311854295196814963)
          ·
            refine ⟨24057103967781442795222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16038069311854295196814963 24057103967781442795222445)
            ·
              refine ⟨9021413987918041048208417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24057103967781442795222445 9021413987918041048208417)
              ·
                refine ⟨6766060490938530786156313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021413987918041048208417 6766060490938530786156313)
                ·
                  refine ⟨5074545368203898089617235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6766060490938530786156313 5074545368203898089617235)
                  ·
                    refine ⟨7611818052305847134425853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074545368203898089617235 7611818052305847134425853)
                    ·
                      refine ⟨2854431769614692675409695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7611818052305847134425853 2854431769614692675409695)
                      ·
                        rfl

theorem cell23_5558986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_5558986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558986 prefixEnd_5558986 := by exact prefixLift 5558986
  have htrace : WordTrace (prefixWord ++ tailWord_5558986) baseStart_5558986 baseEnd_5558986 := by
    simpa [prefixWord, tailWord_5558986, baseEnd_5558986] using wordTrace_append hprefix tailTrace_5558986
  have hstable : (prefixWord ++ tailWord_5558986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558986).length < 2 ^ (prefixWord ++ tailWord_5558986).sum := by decide
  have hdescent : baseEnd_5558986 < baseStart_5558986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559026 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5559026 : Nat := 118140960795 + 5559026 * 2 ^ 59
def prefixEnd_5559026 : Nat := 4983230072969 + 3 ^ 40 * 5559026 * 2
def baseEnd_5559026 : Nat := 2854452308840872518909511

theorem tailTrace_5559026 : CollatzResearch.WordTrace tailWord_5559026 prefixEnd_5559026 2854452308840872518909511 := by
  unfold tailWord_5559026
  simp only [CollatzResearch.WordTrace]
  refine ⟨50688583789651420724958233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135169556772403788599888621 50688583789651420724958233)
  ·
    refine ⟨38016437842238565543718675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50688583789651420724958233 38016437842238565543718675)
    ·
      refine ⟨57024656763357848315578013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38016437842238565543718675 57024656763357848315578013)
      ·
        refine ⟨21384246286259193118341755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57024656763357848315578013 21384246286259193118341755)
        ·
          refine ⟨32076369429388789677512633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21384246286259193118341755 32076369429388789677512633)
          ·
            refine ⟨24057277072041592258134475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32076369429388789677512633 24057277072041592258134475)
            ·
              refine ⟨36085915608062388387201713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24057277072041592258134475 36085915608062388387201713)
              ·
                refine ⟨27064436706046791290401285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36085915608062388387201713 27064436706046791290401285)
                ·
                  refine ⟨5074581882383773366950241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27064436706046791290401285 5074581882383773366950241)
                  ·
                    refine ⟨3805936411787830025212681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074581882383773366950241 3805936411787830025212681)
                    ·
                      refine ⟨2854452308840872518909511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805936411787830025212681 2854452308840872518909511)
                      ·
                        rfl

theorem cell23_5559026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5559026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559026 prefixEnd_5559026 := by exact prefixLift 5559026
  have htrace : WordTrace (prefixWord ++ tailWord_5559026) baseStart_5559026 baseEnd_5559026 := by
    simpa [prefixWord, tailWord_5559026, baseEnd_5559026] using wordTrace_append hprefix tailTrace_5559026
  have hstable : (prefixWord ++ tailWord_5559026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559026).length < 2 ^ (prefixWord ++ tailWord_5559026).sum := by decide
  have hdescent : baseEnd_5559026 < baseStart_5559026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559116 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5559116 : Nat := 118140960795 + 5559116 * 2 ^ 59
def prefixEnd_5559116 : Nat := 4983230072969 + 3 ^ 40 * 5559116 * 2
def baseEnd_5559116 : Nat := 2854498522099777166784097

theorem tailTrace_5559116 : CollatzResearch.WordTrace tailWord_5559116 prefixEnd_5559116 2854498522099777166784097 := by
  unfold tailWord_5559116
  simp only [CollatzResearch.WordTrace]
  refine ⟨101378808864139814135304601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135171745152186418847072801 101378808864139814135304601)
  ·
    refine ⟨76034106648104860601478451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101378808864139814135304601 76034106648104860601478451)
    ·
      refine ⟨114051159972157290902217677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76034106648104860601478451 114051159972157290902217677)
      ·
        refine ⟨42769184989558984088331629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114051159972157290902217677 42769184989558984088331629)
        ·
          refine ⟨16038444371084619033124361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42769184989558984088331629 16038444371084619033124361)
          ·
            refine ⟨12028833278313464274843271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16038444371084619033124361 12028833278313464274843271)
            ·
              refine ⟨18043249917470196412264907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12028833278313464274843271 18043249917470196412264907)
              ·
                refine ⟨27064874876205294618397361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18043249917470196412264907 27064874876205294618397361)
                ·
                  refine ⟨20298656157153970963798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27064874876205294618397361 20298656157153970963798021)
                  ·
                    refine ⟨3805998029466369555712129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20298656157153970963798021 3805998029466369555712129)
                    ·
                      refine ⟨2854498522099777166784097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805998029466369555712129 2854498522099777166784097)
                      ·
                        rfl

theorem cell23_5559116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5559116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559116 prefixEnd_5559116 := by exact prefixLift 5559116
  have htrace : WordTrace (prefixWord ++ tailWord_5559116) baseStart_5559116 baseEnd_5559116 := by
    simpa [prefixWord, tailWord_5559116, baseEnd_5559116] using wordTrace_append hprefix tailTrace_5559116
  have hstable : (prefixWord ++ tailWord_5559116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559116).length < 2 ^ (prefixWord ++ tailWord_5559116).sum := by decide
  have hdescent : baseEnd_5559116 < baseStart_5559116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559143 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5559143 : Nat := 118140960795 + 5559143 * 2 ^ 59
def prefixEnd_5559143 : Nat := 4983230072969 + 3 ^ 40 * 5559143 * 2
def baseEnd_5559143 : Nat := 951504128692482853715491

theorem tailTrace_5559143 : CollatzResearch.WordTrace tailWord_5559143 prefixEnd_5559143 951504128692482853715491 := by
  unfold tailWord_5559143
  simp only [CollatzResearch.WordTrace]
  refine ⟨202758602499181811881842083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135172401666121207921228055 202758602499181811881842083)
  ·
    refine ⟨304137903748772717822763125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202758602499181811881842083 304137903748772717822763125)
    ·
      refine ⟨28512928476447442295884043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304137903748772717822763125 28512928476447442295884043)
      ·
        refine ⟨42769392714671163443826065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28512928476447442295884043 42769392714671163443826065)
        ·
          refine ⟨32077044536003372582869549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42769392714671163443826065 32077044536003372582869549)
          ·
            refine ⟨12028891701001264718576081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32077044536003372582869549 12028891701001264718576081)
            ·
              refine ⟨9021668775750948538932061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12028891701001264718576081 9021668775750948538932061)
              ·
                refine ⟨3383125790906605702099523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9021668775750948538932061 3383125790906605702099523)
                ·
                  refine ⟨5074688686359908553149285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383125790906605702099523 5074688686359908553149285)
                  ·
                    refine ⟨951504128692482853715491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074688686359908553149285 951504128692482853715491)
                    ·
                      rfl

theorem cell23_5559143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5559143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559143 prefixEnd_5559143 := by exact prefixLift 5559143
  have htrace : WordTrace (prefixWord ++ tailWord_5559143) baseStart_5559143 baseEnd_5559143 := by
    simpa [prefixWord, tailWord_5559143, baseEnd_5559143] using wordTrace_append hprefix tailTrace_5559143
  have hstable : (prefixWord ++ tailWord_5559143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559143).length < 2 ^ (prefixWord ++ tailWord_5559143).sum := by decide
  have hdescent : baseEnd_5559143 < baseStart_5559143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559176 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5559176 : Nat := 118140960795 + 5559176 * 2 ^ 59
def prefixEnd_5559176 : Nat := 4983230072969 + 3 ^ 40 * 5559176 * 2
def baseEnd_5559176 : Nat := 2854529330939046932033821

theorem tailTrace_5559176 : CollatzResearch.WordTrace tailWord_5559176 prefixEnd_5559176 2854529330939046932033821 := by
  unfold tailWord_5559176
  simp only [CollatzResearch.WordTrace]
  refine ⟨101379903054031129258896691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135173204072041505678528921 101379903054031129258896691)
  ·
    refine ⟨152069854581046693888345037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101379903054031129258896691 152069854581046693888345037)
    ·
      refine ⟨57026195467892510208129389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152069854581046693888345037 57026195467892510208129389)
      ·
        refine ⟨21384823300459691328048521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57026195467892510208129389 21384823300459691328048521)
        ·
          refine ⟨16038617475344768496036391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21384823300459691328048521 16038617475344768496036391)
          ·
            refine ⟨24057926213017152744054587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16038617475344768496036391 24057926213017152744054587)
            ·
              refine ⟨36086889319525729116081881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24057926213017152744054587 36086889319525729116081881)
              ·
                refine ⟨27065166989644296837061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36086889319525729116081881 27065166989644296837061411)
                ·
                  refine ⟨40597750484466445255592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27065166989644296837061411 40597750484466445255592117)
                  ·
                    refine ⟨3806039107918729242711761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40597750484466445255592117 3806039107918729242711761)
                    ·
                      refine ⟨2854529330939046932033821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806039107918729242711761 2854529330939046932033821)
                      ·
                        rfl

theorem cell23_5559176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5559176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559176 prefixEnd_5559176 := by exact prefixLift 5559176
  have htrace : WordTrace (prefixWord ++ tailWord_5559176) baseStart_5559176 baseEnd_5559176 := by
    simpa [prefixWord, tailWord_5559176, baseEnd_5559176] using wordTrace_append hprefix tailTrace_5559176
  have hstable : (prefixWord ++ tailWord_5559176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559176).length < 2 ^ (prefixWord ++ tailWord_5559176).sum := by decide
  have hdescent : baseEnd_5559176 < baseStart_5559176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559209 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_5559209 : Nat := 118140960795 + 5559209 * 2 ^ 59
def prefixEnd_5559209 : Nat := 4983230072969 + 3 ^ 40 * 5559209 * 2
def baseEnd_5559209 : Nat := 2854546275800645302921169

theorem tailTrace_5559209 : CollatzResearch.WordTrace tailWord_5559209 prefixEnd_5559209 2854546275800645302921169 := by
  unfold tailWord_5559209
  simp only [CollatzResearch.WordTrace]
  refine ⟨202761009716942705153744681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135174006477961803435829787 202761009716942705153744681)
  ·
    refine ⟨152070757287707028865308511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202761009716942705153744681 152070757287707028865308511)
    ·
      refine ⟨228106135931560543297962767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152070757287707028865308511 228106135931560543297962767)
      ·
        refine ⟨342159203897340814946944151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228106135931560543297962767 342159203897340814946944151)
        ·
          refine ⟨513238805846011222420416227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342159203897340814946944151 513238805846011222420416227)
          ·
            refine ⟨769858208769016833630624341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513238805846011222420416227 769858208769016833630624341)
            ·
              refine ⟨9021775884011916019108879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 769858208769016833630624341 9021775884011916019108879)
              ·
                refine ⟨13532663826017874028663319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9021775884011916019108879 13532663826017874028663319)
                ·
                  refine ⟨20298995739026811042994979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13532663826017874028663319 20298995739026811042994979)
                  ·
                    refine ⟨30448493608540216564492469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20298995739026811042994979 30448493608540216564492469)
                    ·
                      refine ⟨2854546275800645302921169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30448493608540216564492469 2854546275800645302921169)
                      ·
                        rfl

theorem cell23_5559209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_5559209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559209 prefixEnd_5559209 := by exact prefixLift 5559209
  have htrace : WordTrace (prefixWord ++ tailWord_5559209) baseStart_5559209 baseEnd_5559209 := by
    simpa [prefixWord, tailWord_5559209, baseEnd_5559209] using wordTrace_append hprefix tailTrace_5559209
  have hstable : (prefixWord ++ tailWord_5559209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559209).length < 2 ^ (prefixWord ++ tailWord_5559209).sum := by decide
  have hdescent : baseEnd_5559209 < baseStart_5559209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559217 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5559217 : Nat := 118140960795 + 5559217 * 2 ^ 59
def prefixEnd_5559217 : Nat := 4983230072969 + 3 ^ 40 * 5559217 * 2
def baseEnd_5559217 : Nat := 2854550383645881271621133

theorem tailTrace_5559217 : CollatzResearch.WordTrace tailWord_5559217 prefixEnd_5559217 2854550383645881271621133 := by
  unfold tailWord_5559217
  simp only [CollatzResearch.WordTrace]
  refine ⟨202761301500913722520035905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135174201000609148346690603 202761301500913722520035905)
  ·
    refine ⟨152070976125685291890026929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202761301500913722520035905 152070976125685291890026929)
    ·
      refine ⟨114053232094263968917520197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152070976125685291890026929 114053232094263968917520197)
      ·
        refine ⟨21384981017674494172035037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114053232094263968917520197 21384981017674494172035037)
        ·
          refine ⟨8019367881627935314513139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21384981017674494172035037 8019367881627935314513139)
          ·
            refine ⟨12029051822441902971769709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019367881627935314513139 12029051822441902971769709)
            ·
              refine ⟨4510894433415713614413641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12029051822441902971769709 4510894433415713614413641)
              ·
                refine ⟨3383170825061785210810231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510894433415713614413641 3383170825061785210810231)
                ·
                  refine ⟨5074756237592677816215347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383170825061785210810231 5074756237592677816215347)
                  ·
                    refine ⟨7612134356389016724323021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074756237592677816215347 7612134356389016724323021)
                    ·
                      refine ⟨2854550383645881271621133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612134356389016724323021 2854550383645881271621133)
                      ·
                        rfl

theorem cell23_5559217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5559217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559217 prefixEnd_5559217 := by exact prefixLift 5559217
  have htrace : WordTrace (prefixWord ++ tailWord_5559217) baseStart_5559217 baseEnd_5559217 := by
    simpa [prefixWord, tailWord_5559217, baseEnd_5559217] using wordTrace_append hprefix tailTrace_5559217
  have hstable : (prefixWord ++ tailWord_5559217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559217).length < 2 ^ (prefixWord ++ tailWord_5559217).sum := by decide
  have hdescent : baseEnd_5559217 < baseStart_5559217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559223 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_5559223 : Nat := 118140960795 + 5559223 * 2 ^ 59
def prefixEnd_5559223 : Nat := 4983230072969 + 3 ^ 40 * 5559223 * 2
def baseEnd_5559223 : Nat := 2854553464529808248146105

theorem tailTrace_5559223 : CollatzResearch.WordTrace tailWord_5559223 prefixEnd_5559223 2854553464529808248146105 := by
  unfold tailWord_5559223
  simp only [CollatzResearch.WordTrace]
  refine ⟨202761520338891985544754323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135174346892594657029836215 202761520338891985544754323)
  ·
    refine ⟨304142280508337978317131485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202761520338891985544754323 304142280508337978317131485)
    ·
      refine ⟨114053355190626741868924307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304142280508337978317131485 114053355190626741868924307)
      ·
        refine ⟨171080032785940112803386461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114053355190626741868924307 171080032785940112803386461)
        ·
          refine ⟨64155012294727542301269923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171080032785940112803386461 64155012294727542301269923)
          ·
            refine ⟨96232518442091313451904885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64155012294727542301269923 96232518442091313451904885)
            ·
              refine ⟨9021798603946060636116083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96232518442091313451904885 9021798603946060636116083)
              ·
                refine ⟨13532697905919090954174125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9021798603946060636116083 13532697905919090954174125)
                ·
                  refine ⟨5074761714719659107815297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13532697905919090954174125 5074761714719659107815297)
                  ·
                    refine ⟨3806071286039744330861473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074761714719659107815297 3806071286039744330861473)
                    ·
                      refine ⟨2854553464529808248146105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806071286039744330861473 2854553464529808248146105)
                      ·
                        rfl

theorem cell23_5559223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_5559223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559223 prefixEnd_5559223 := by exact prefixLift 5559223
  have htrace : WordTrace (prefixWord ++ tailWord_5559223) baseStart_5559223 baseEnd_5559223 := by
    simpa [prefixWord, tailWord_5559223, baseEnd_5559223] using wordTrace_append hprefix tailTrace_5559223
  have hstable : (prefixWord ++ tailWord_5559223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559223).length < 2 ^ (prefixWord ++ tailWord_5559223).sum := by decide
  have hdescent : baseEnd_5559223 < baseStart_5559223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559240 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_5559240 : Nat := 118140960795 + 5559240 * 2 ^ 59
def prefixEnd_5559240 : Nat := 4983230072969 + 3 ^ 40 * 5559240 * 2
def baseEnd_5559240 : Nat := 2854562193700934681633527

theorem tailTrace_5559240 : CollatzResearch.WordTrace tailWord_5559240 prefixEnd_5559240 2854562193700934681633527 := by
  unfold tailWord_5559240
  simp only [CollatzResearch.WordTrace]
  refine ⟨101381070189915198724061587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135174760253220264965415449 101381070189915198724061587)
  ·
    refine ⟨152071605284872798086092381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101381070189915198724061587 152071605284872798086092381)
    ·
      refine ⟨57026851981827299282284643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152071605284872798086092381 57026851981827299282284643)
      ·
        refine ⟨85540277972740948923426965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57026851981827299282284643 85540277972740948923426965)
        ·
          refine ⟨4009700529972231980785639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85540277972740948923426965 4009700529972231980785639)
          ·
            refine ⟨6014550794958347971178459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009700529972231980785639 6014550794958347971178459)
            ·
              refine ⟨9021826192437521956767689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014550794958347971178459 9021826192437521956767689)
              ·
                refine ⟨6766369644328141467575767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021826192437521956767689 6766369644328141467575767)
                ·
                  refine ⟨10149554466492212201363651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766369644328141467575767 10149554466492212201363651)
                  ·
                    refine ⟨15224331699738318302045477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10149554466492212201363651 15224331699738318302045477)
                    ·
                      refine ⟨2854562193700934681633527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15224331699738318302045477 2854562193700934681633527)
                      ·
                        rfl

theorem cell23_5559240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_5559240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559240 prefixEnd_5559240 := by exact prefixLift 5559240
  have htrace : WordTrace (prefixWord ++ tailWord_5559240) baseStart_5559240 baseEnd_5559240 := by
    simpa [prefixWord, tailWord_5559240, baseEnd_5559240] using wordTrace_append hprefix tailTrace_5559240
  have hstable : (prefixWord ++ tailWord_5559240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559240).length < 2 ^ (prefixWord ++ tailWord_5559240).sum := by decide
  have hdescent : baseEnd_5559240 < baseStart_5559240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559243 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 3]
def baseStart_5559243 : Nat := 118140960795 + 5559243 * 2 ^ 59
def prefixEnd_5559243 : Nat := 4983230072969 + 3 ^ 40 * 5559243 * 2
def baseEnd_5559243 : Nat := 2854563734142898169896013

theorem tailTrace_5559243 : CollatzResearch.WordTrace tailWord_5559243 prefixEnd_5559243 2854563734142898169896013 := by
  unfold tailWord_5559243
  simp only [CollatzResearch.WordTrace]
  refine ⟨202762249798819528960482383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135174833199213019306988255 202762249798819528960482383)
  ·
    refine ⟨304143374698229293440723575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202762249798819528960482383 304143374698229293440723575)
    ·
      refine ⟨456215062047343940161085363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304143374698229293440723575 456215062047343940161085363)
      ·
        refine ⟨684322593071015910241628045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456215062047343940161085363 684322593071015910241628045)
        ·
          refine ⟨256620972401630966340610517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684322593071015910241628045 256620972401630966340610517)
          ·
            refine ⟨6014554040663225773608059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 256620972401630966340610517 6014554040663225773608059)
            ·
              refine ⟨9021831060994838660412089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014554040663225773608059 9021831060994838660412089)
              ·
                refine ⟨6766373295746128995309067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021831060994838660412089 6766373295746128995309067)
                ·
                  refine ⟨10149559943619193492963601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766373295746128995309067 10149559943619193492963601)
                  ·
                    refine ⟨7612169957714395119722701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10149559943619193492963601 7612169957714395119722701)
                    ·
                      refine ⟨2854563734142898169896013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612169957714395119722701 2854563734142898169896013)
                      ·
                        rfl

theorem cell23_5559243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 3].length) (baseStart_5559243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559243 prefixEnd_5559243 := by exact prefixLift 5559243
  have htrace : WordTrace (prefixWord ++ tailWord_5559243) baseStart_5559243 baseEnd_5559243 := by
    simpa [prefixWord, tailWord_5559243, baseEnd_5559243] using wordTrace_append hprefix tailTrace_5559243
  have hstable : (prefixWord ++ tailWord_5559243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559243).length < 2 ^ (prefixWord ++ tailWord_5559243).sum := by decide
  have hdescent : baseEnd_5559243 < baseStart_5559243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559256 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_5559256 : Nat := 118140960795 + 5559256 * 2 ^ 59
def prefixEnd_5559256 : Nat := 4983230072969 + 3 ^ 40 * 5559256 * 2
def baseEnd_5559256 : Nat := 2854570409391406619033453

theorem tailTrace_5559256 : CollatzResearch.WordTrace tailWord_5559256 prefixEnd_5559256 2854570409391406619033453 := by
  unfold tailWord_5559256
  simp only [CollatzResearch.WordTrace]
  refine ⟨101381361973886216090352811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135175149298514954787137081 101381361973886216090352811)
  ·
    refine ⟨152072042960829324135529217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101381361973886216090352811 152072042960829324135529217)
    ·
      refine ⟨114054032220621993101646913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152072042960829324135529217 114054032220621993101646913)
      ·
        refine ⟨85540524165466494826235185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114054032220621993101646913 85540524165466494826235185)
        ·
          refine ⟨64155393124099871119676389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85540524165466494826235185 64155393124099871119676389)
          ·
            refine ⟨12029136210768725834939323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64155393124099871119676389 12029136210768725834939323)
            ·
              refine ⟨18043704316153088752408985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029136210768725834939323 18043704316153088752408985)
              ·
                refine ⟨13532778237114816564306739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18043704316153088752408985 13532778237114816564306739)
                ·
                  refine ⟨20299167355672224846460109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13532778237114816564306739 20299167355672224846460109)
                  ·
                    refine ⟨7612187758377084317422541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20299167355672224846460109 7612187758377084317422541)
                    ·
                      refine ⟨2854570409391406619033453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612187758377084317422541 2854570409391406619033453)
                      ·
                        rfl

theorem cell23_5559256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_5559256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559256 prefixEnd_5559256 := by exact prefixLift 5559256
  have htrace : WordTrace (prefixWord ++ tailWord_5559256) baseStart_5559256 baseEnd_5559256 := by
    simpa [prefixWord, tailWord_5559256, baseEnd_5559256] using wordTrace_append hprefix tailTrace_5559256
  have hstable : (prefixWord ++ tailWord_5559256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559256).length < 2 ^ (prefixWord ++ tailWord_5559256).sum := by decide
  have hdescent : baseEnd_5559256 < baseStart_5559256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559274 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_5559274 : Nat := 118140960795 + 5559274 * 2 ^ 59
def prefixEnd_5559274 : Nat := 4983230072969 + 3 ^ 40 * 5559274 * 2
def baseEnd_5559274 : Nat := 2854579652043187548608371

theorem tailTrace_5559274 : CollatzResearch.WordTrace tailWord_5559274 prefixEnd_5559274 2854579652043187548608371 := by
  unfold tailWord_5559274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50690845115426805313715219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135175586974471480836573917 50690845115426805313715219)
  ·
    refine ⟨76036267673140207970572829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50690845115426805313715219 76036267673140207970572829)
    ·
      refine ⟨28513600377427577988964811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76036267673140207970572829 28513600377427577988964811)
      ·
        refine ⟨42770400566141366983447217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28513600377427577988964811 42770400566141366983447217)
        ·
          refine ⟨32077800424606025237585413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42770400566141366983447217 32077800424606025237585413)
          ·
            refine ⟨6014587579613629732047265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32077800424606025237585413 6014587579613629732047265)
            ·
              refine ⟨4510940684710222299035449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014587579613629732047265 4510940684710222299035449)
              ·
                refine ⟨3383205513532666724276587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510940684710222299035449 3383205513532666724276587)
                ·
                  refine ⟨5074808270299000086414881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383205513532666724276587 5074808270299000086414881)
                  ·
                    refine ⟨3806106202724250064811161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074808270299000086414881 3806106202724250064811161)
                    ·
                      refine ⟨2854579652043187548608371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806106202724250064811161 2854579652043187548608371)
                      ·
                        rfl

theorem cell23_5559274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_5559274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559274 prefixEnd_5559274 := by exact prefixLift 5559274
  have htrace : WordTrace (prefixWord ++ tailWord_5559274) baseStart_5559274 baseEnd_5559274 := by
    simpa [prefixWord, tailWord_5559274, baseEnd_5559274] using wordTrace_append hprefix tailTrace_5559274
  have hstable : (prefixWord ++ tailWord_5559274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559274).length < 2 ^ (prefixWord ++ tailWord_5559274).sum := by decide
  have hdescent : baseEnd_5559274 < baseStart_5559274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559279 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_5559279 : Nat := 118140960795 + 5559279 * 2 ^ 59
def prefixEnd_5559279 : Nat := 4983230072969 + 3 ^ 40 * 5559279 * 2
def baseEnd_5559279 : Nat := 2854582219446460029045847

theorem tailTrace_5559279 : CollatzResearch.WordTrace tailWord_5559279 prefixEnd_5559279 2854582219446460029045847 := by
  unfold tailWord_5559279
  simp only [CollatzResearch.WordTrace]
  refine ⟨202763562826689107108792891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135175708551126071405861927 202763562826689107108792891)
  ·
    refine ⟨304145344240033660663189337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202763562826689107108792891 304145344240033660663189337)
    ·
      refine ⟨228109008180025245497392003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304145344240033660663189337 228109008180025245497392003)
      ·
        refine ⟨342163512270037868246088005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228109008180025245497392003 342163512270037868246088005)
        ·
          refine ⟨64155658550632100296141501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342163512270037868246088005 64155658550632100296141501)
          ·
            refine ⟨24058371956487037611053063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64155658550632100296141501 24058371956487037611053063)
            ·
              refine ⟨36087557934730556416579595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24058371956487037611053063 36087557934730556416579595)
              ·
                refine ⟨54131336902095834624869393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36087557934730556416579595 54131336902095834624869393)
                ·
                  refine ⟨40598502676571875968652045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54131336902095834624869393 40598502676571875968652045)
                  ·
                    refine ⟨15224438503714453488244517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40598502676571875968652045 15224438503714453488244517)
                    ·
                      refine ⟨2854582219446460029045847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15224438503714453488244517 2854582219446460029045847)
                      ·
                        rfl

theorem cell23_5559279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_5559279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559279 prefixEnd_5559279 := by exact prefixLift 5559279
  have htrace : WordTrace (prefixWord ++ tailWord_5559279) baseStart_5559279 baseEnd_5559279 := by
    simpa [prefixWord, tailWord_5559279, baseEnd_5559279] using wordTrace_append hprefix tailTrace_5559279
  have hstable : (prefixWord ++ tailWord_5559279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559279).length < 2 ^ (prefixWord ++ tailWord_5559279).sum := by decide
  have hdescent : baseEnd_5559279 < baseStart_5559279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559289 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_5559289 : Nat := 118140960795 + 5559289 * 2 ^ 59
def prefixEnd_5559289 : Nat := 4983230072969 + 3 ^ 40 * 5559289 * 2
def baseEnd_5559289 : Nat := 951529118084334996640267

theorem tailTrace_5559289 : CollatzResearch.WordTrace tailWord_5559289 prefixEnd_5559289 951529118084334996640267 := by
  unfold tailWord_5559289
  simp only [CollatzResearch.WordTrace]
  refine ⟨202763927556652878816656921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135175951704435252544437947 202763927556652878816656921)
  ·
    refine ⟨152072945667489659112492691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202763927556652878816656921 152072945667489659112492691)
    ·
      refine ⟨228109418501234488668739037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152072945667489659112492691 228109418501234488668739037)
      ·
        refine ⟨85541031937962933250777139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228109418501234488668739037 85541031937962933250777139)
        ·
          refine ⟨128311547906944399876165709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85541031937962933250777139 128311547906944399876165709)
          ·
            refine ⟨48116830465104149953562141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128311547906944399876165709 48116830465104149953562141)
            ·
              refine ⟨18043811424414056232585803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48116830465104149953562141 18043811424414056232585803)
              ·
                refine ⟨27065717136621084348878705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18043811424414056232585803 27065717136621084348878705)
                ·
                  refine ⟨20299287852465813261659029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27065717136621084348878705 20299287852465813261659029)
                  ·
                    refine ⟨951529118084334996640267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20299287852465813261659029 951529118084334996640267)
                    ·
                      rfl

theorem cell23_5559289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_5559289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559289 prefixEnd_5559289 := by exact prefixLift 5559289
  have htrace : WordTrace (prefixWord ++ tailWord_5559289) baseStart_5559289 baseEnd_5559289 := by
    simpa [prefixWord, tailWord_5559289, baseEnd_5559289] using wordTrace_append hprefix tailTrace_5559289
  have hstable : (prefixWord ++ tailWord_5559289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559289).length < 2 ^ (prefixWord ++ tailWord_5559289).sum := by decide
  have hdescent : baseEnd_5559289 < baseStart_5559289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559317 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_5559317 : Nat := 118140960795 + 5559317 * 2 ^ 59
def prefixEnd_5559317 : Nat := 4983230072969 + 3 ^ 40 * 5559317 * 2
def baseEnd_5559317 : Nat := 2854601731711330880370673

theorem tailTrace_5559317 : CollatzResearch.WordTrace tailWord_5559317 prefixEnd_5559317 2854601731711330880370673 := by
  unfold tailWord_5559317
  simp only [CollatzResearch.WordTrace]
  refine ⟨202764948800551439598676205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135176632533700959732450803 202764948800551439598676205)
  ·
    refine ⟨76036855800206789849503577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202764948800551439598676205 76036855800206789849503577)
    ·
      refine ⟨57027641850155092387127683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76036855800206789849503577 57027641850155092387127683)
      ·
        refine ⟨85541462775232638580691525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57027641850155092387127683 85541462775232638580691525)
        ·
          refine ⟨16039024270356119733879661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85541462775232638580691525 16039024270356119733879661)
          ·
            refine ⟨6014634101383544900204873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16039024270356119733879661 6014634101383544900204873)
            ·
              refine ⟨4510975576037658675153655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014634101383544900204873 4510975576037658675153655)
              ·
                refine ⟨6766463364056488012730483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510975576037658675153655 6766463364056488012730483)
                ·
                  refine ⟨10149695046084732019095725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766463364056488012730483 10149695046084732019095725)
                  ·
                    refine ⟨3806135642281774507160897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10149695046084732019095725 3806135642281774507160897)
                    ·
                      refine ⟨2854601731711330880370673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806135642281774507160897 2854601731711330880370673)
                      ·
                        rfl

theorem cell23_5559317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_5559317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559317 prefixEnd_5559317 := by exact prefixLift 5559317
  have htrace : WordTrace (prefixWord ++ tailWord_5559317) baseStart_5559317 baseEnd_5559317 := by
    simpa [prefixWord, tailWord_5559317, baseEnd_5559317] using wordTrace_append hprefix tailTrace_5559317
  have hstable : (prefixWord ++ tailWord_5559317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559317).length < 2 ^ (prefixWord ++ tailWord_5559317).sum := by decide
  have hdescent : baseEnd_5559317 < baseStart_5559317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559330 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_5559330 : Nat := 118140960795 + 5559330 * 2 ^ 59
def prefixEnd_5559330 : Nat := 4983230072969 + 3 ^ 40 * 5559330 * 2
def baseEnd_5559330 : Nat := 2854608406959839329508113

theorem tailTrace_5559330 : CollatzResearch.WordTrace tailWord_5559330 prefixEnd_5559330 2854608406959839329508113 := by
  unfold tailWord_5559330
  simp only [CollatzResearch.WordTrace]
  refine ⟨50691355737376085704724861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135176948633002895212599629 50691355737376085704724861)
  ·
    refine ⟨19009258401516032139271823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50691355737376085704724861 19009258401516032139271823)
    ·
      refine ⟨28513887602274048208907735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19009258401516032139271823 28513887602274048208907735)
      ·
        refine ⟨42770831403411072313361603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28513887602274048208907735 42770831403411072313361603)
        ·
          refine ⟨64156247105116608470042405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42770831403411072313361603 64156247105116608470042405)
          ·
            refine ⟨12029296332209364088132951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64156247105116608470042405 12029296332209364088132951)
            ·
              refine ⟨18043944498314046132199427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029296332209364088132951 18043944498314046132199427)
              ·
                refine ⟨27065916747471069198299141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18043944498314046132199427 27065916747471069198299141)
                ·
                  refine ⟨5074859390150825474681089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27065916747471069198299141 5074859390150825474681089)
                  ·
                    refine ⟨3806144542613119106010817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074859390150825474681089 3806144542613119106010817)
                    ·
                      refine ⟨2854608406959839329508113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806144542613119106010817 2854608406959839329508113)
                      ·
                        rfl

theorem cell23_5559330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_5559330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559330 prefixEnd_5559330 := by exact prefixLift 5559330
  have htrace : WordTrace (prefixWord ++ tailWord_5559330) baseStart_5559330 baseEnd_5559330 := by
    simpa [prefixWord, tailWord_5559330, baseEnd_5559330] using wordTrace_append hprefix tailTrace_5559330
  have hstable : (prefixWord ++ tailWord_5559330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559330).length < 2 ^ (prefixWord ++ tailWord_5559330).sum := by decide
  have hdescent : baseEnd_5559330 < baseStart_5559330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559346 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_5559346 : Nat := 118140960795 + 5559346 * 2 ^ 59
def prefixEnd_5559346 : Nat := 4983230072969 + 3 ^ 40 * 5559346 * 2
def baseEnd_5559346 : Nat := 2854616622650311266908039

theorem tailTrace_5559346 : CollatzResearch.WordTrace tailWord_5559346 prefixEnd_5559346 2854616622650311266908039 := by
  unfold tailWord_5559346
  simp only [CollatzResearch.WordTrace]
  refine ⟨50691501629361594387870473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135177337678297585034321261 50691501629361594387870473)
  ·
    refine ⟨38018626222021195790902855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50691501629361594387870473 38018626222021195790902855)
    ·
      refine ⟨57027939333031793686354283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38018626222021195790902855 57027939333031793686354283)
      ·
        refine ⟨85541908999547690529531425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57027939333031793686354283 85541908999547690529531425)
        ·
          refine ⟨64156431749660767897148569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85541908999547690529531425 64156431749660767897148569)
          ·
            refine ⟨48117323812245575922861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64156431749660767897148569 48117323812245575922861427)
            ·
              refine ⟨72175985718368363884292141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48117323812245575922861427 72175985718368363884292141)
              ·
                refine ⟨27065994644388136456609553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72175985718368363884292141 27065994644388136456609553)
                ·
                  refine ⟨20299495983291102342457165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27065994644388136456609553 20299495983291102342457165)
                  ·
                    refine ⟨7612310993734163378421437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20299495983291102342457165 7612310993734163378421437)
                    ·
                      refine ⟨2854616622650311266908039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612310993734163378421437 2854616622650311266908039)
                      ·
                        rfl

theorem cell23_5559346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_5559346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559346 prefixEnd_5559346 := by exact prefixLift 5559346
  have htrace : WordTrace (prefixWord ++ tailWord_5559346) baseStart_5559346 baseEnd_5559346 := by
    simpa [prefixWord, tailWord_5559346, baseEnd_5559346] using wordTrace_append hprefix tailTrace_5559346
  have hstable : (prefixWord ++ tailWord_5559346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559346).length < 2 ^ (prefixWord ++ tailWord_5559346).sum := by decide
  have hdescent : baseEnd_5559346 < baseStart_5559346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559359 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_5559359 : Nat := 118140960795 + 5559359 * 2 ^ 59
def prefixEnd_5559359 : Nat := 4983230072969 + 3 ^ 40 * 5559359 * 2
def baseEnd_5559359 : Nat := 2854623297898819716045479

theorem tailTrace_5559359 : CollatzResearch.WordTrace tailWord_5559359 prefixEnd_5559359 2854623297898819716045479 := by
  unfold tailWord_5559359
  simp only [CollatzResearch.WordTrace]
  refine ⟨202766480666399280771705131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135177653777599520514470087 202766480666399280771705131)
  ·
    refine ⟨304149720999598921157557697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202766480666399280771705131 304149720999598921157557697)
    ·
      refine ⟨228112290749699190868168273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304149720999598921157557697 228112290749699190868168273)
      ·
        refine ⟨171084218062274393151126205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228112290749699190868168273 171084218062274393151126205)
        ·
          refine ⟨64156581773352897431672327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171084218062274393151126205 64156581773352897431672327)
          ·
            refine ⟨96234872660029346147508491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64156581773352897431672327 96234872660029346147508491)
            ·
              refine ⟨144352308990044019221262737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96234872660029346147508491 144352308990044019221262737)
              ·
                refine ⟨108264231742533014415947053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144352308990044019221262737 108264231742533014415947053)
                ·
                  refine ⟨40599086903449880405980145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108264231742533014415947053 40599086903449880405980145)
                  ·
                    refine ⟨30449315177587410304485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40599086903449880405980145 30449315177587410304485109)
                    ·
                      refine ⟨2854623297898819716045479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30449315177587410304485109 2854623297898819716045479)
                      ·
                        rfl

theorem cell23_5559359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_5559359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559359 prefixEnd_5559359 := by exact prefixLift 5559359
  have htrace : WordTrace (prefixWord ++ tailWord_5559359) baseStart_5559359 baseEnd_5559359 := by
    simpa [prefixWord, tailWord_5559359, baseEnd_5559359] using wordTrace_append hprefix tailTrace_5559359
  have hstable : (prefixWord ++ tailWord_5559359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559359).length < 2 ^ (prefixWord ++ tailWord_5559359).sum := by decide
  have hdescent : baseEnd_5559359 < baseStart_5559359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559409 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 10]
def baseStart_5559409 : Nat := 118140960795 + 5559409 * 2 ^ 59
def prefixEnd_5559409 : Nat := 4983230072969 + 3 ^ 40 * 5559409 * 2
def baseEnd_5559409 : Nat := 317183219103504946713361

theorem tailTrace_5559409 : CollatzResearch.WordTrace tailWord_5559409 prefixEnd_5559409 317183219103504946713361 := by
  unfold tailWord_5559409
  simp only [CollatzResearch.WordTrace]
  refine ⟨202768304316218139311025281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135178869544145426207350187 202768304316218139311025281)
  ·
    refine ⟨152076228237163604483268961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202768304316218139311025281 152076228237163604483268961)
    ·
      refine ⟨114057171177872703362451721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152076228237163604483268961 114057171177872703362451721)
      ·
        refine ⟨85542878383404527521838791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114057171177872703362451721 85542878383404527521838791)
        ·
          refine ⟨128314317575106791282758187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85542878383404527521838791 128314317575106791282758187)
          ·
            refine ⟨192471476362660186924137281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128314317575106791282758187 192471476362660186924137281)
            ·
              refine ⟨144353607271995140193102961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192471476362660186924137281 144353607271995140193102961)
              ·
                refine ⟨108265205453996355144827221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144353607271995140193102961 108265205453996355144827221)
                ·
                  refine ⟨317183219103504946713361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 108265205453996355144827221 317183219103504946713361)
                  ·
                    rfl

theorem cell23_5559409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_5559409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559409 prefixEnd_5559409 := by exact prefixLift 5559409
  have htrace : WordTrace (prefixWord ++ tailWord_5559409) baseStart_5559409 baseEnd_5559409 := by
    simpa [prefixWord, tailWord_5559409, baseEnd_5559409] using wordTrace_append hprefix tailTrace_5559409
  have hstable : (prefixWord ++ tailWord_5559409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559409).length < 2 ^ (prefixWord ++ tailWord_5559409).sum := by decide
  have hdescent : baseEnd_5559409 < baseStart_5559409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559439 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 9]
def baseStart_5559439 : Nat := 118140960795 + 5559439 * 2 ^ 59
def prefixEnd_5559439 : Nat := 4983230072969 + 3 ^ 40 * 5559439 * 2
def baseEnd_5559439 : Nat := 951554792117059801015037

theorem tailTrace_5559439 : CollatzResearch.WordTrace tailWord_5559439 prefixEnd_5559439 951554792117059801015037 := by
  unfold tailWord_5559439
  simp only [CollatzResearch.WordTrace]
  refine ⟨202769398506109454434617371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135179599004072969623078247 202769398506109454434617371)
  ·
    refine ⟨304154097759164181651926057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202769398506109454434617371 304154097759164181651926057)
    ·
      refine ⟨228115573319373136238944543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304154097759164181651926057 228115573319373136238944543)
      ·
        refine ⟨342173359979059704358416815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228115573319373136238944543 342173359979059704358416815)
        ·
          refine ⟨513260039968589556537625223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342173359979059704358416815 513260039968589556537625223)
          ·
            refine ⟨769890059952884334806437835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513260039968589556537625223 769890059952884334806437835)
            ·
              refine ⟨1154835089929326502209656753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769890059952884334806437835 1154835089929326502209656753)
              ·
                refine ⟨866126317446994876657242565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154835089929326502209656753 866126317446994876657242565)
                ·
                  refine ⟨162398684521311539373232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866126317446994876657242565 162398684521311539373232981)
                  ·
                    refine ⟨951554792117059801015037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162398684521311539373232981 951554792117059801015037)
                    ·
                      rfl

theorem cell23_5559439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_5559439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559439 prefixEnd_5559439 := by exact prefixLift 5559439
  have htrace : WordTrace (prefixWord ++ tailWord_5559439) baseStart_5559439 baseEnd_5559439 := by
    simpa [prefixWord, tailWord_5559439, baseEnd_5559439] using wordTrace_append hprefix tailTrace_5559439
  have hstable : (prefixWord ++ tailWord_5559439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559439).length < 2 ^ (prefixWord ++ tailWord_5559439).sum := by decide
  have hdescent : baseEnd_5559439 < baseStart_5559439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559447 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 1, 4]
def baseStart_5559447 : Nat := 118140960795 + 5559447 * 2 ^ 59
def prefixEnd_5559447 : Nat := 4983230072969 + 3 ^ 40 * 5559447 * 2
def baseEnd_5559447 : Nat := 951556161398805123915025

theorem tailTrace_5559447 : CollatzResearch.WordTrace tailWord_5559447 prefixEnd_5559447 951556161398805123915025 := by
  unfold tailWord_5559447
  simp only [CollatzResearch.WordTrace]
  refine ⟨202769690290080471800908595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135179793526720314533939063 202769690290080471800908595)
  ·
    refine ⟨304154535435120707701362893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202769690290080471800908595 304154535435120707701362893)
    ·
      refine ⟨114057950788170265388011085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304154535435120707701362893 114057950788170265388011085)
      ·
        refine ⟨42771731545563849520504157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114057950788170265388011085 42771731545563849520504157)
        ·
          refine ⟨16039399329586443570189059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42771731545563849520504157 16039399329586443570189059)
          ·
            refine ⟨24059098994379665355283589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16039399329586443570189059 24059098994379665355283589)
            ·
              refine ⟨4511081061446187254115673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24059098994379665355283589 4511081061446187254115673)
              ·
                refine ⟨3383310796084640440586755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511081061446187254115673 3383310796084640440586755)
                ·
                  refine ⟨5074966194126960660880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383310796084640440586755 5074966194126960660880133)
                  ·
                    refine ⟨951556161398805123915025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074966194126960660880133 951556161398805123915025)
                    ·
                      rfl

theorem cell23_5559447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_5559447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559447 prefixEnd_5559447 := by exact prefixLift 5559447
  have htrace : WordTrace (prefixWord ++ tailWord_5559447) baseStart_5559447 baseEnd_5559447 := by
    simpa [prefixWord, tailWord_5559447, baseEnd_5559447] using wordTrace_append hprefix tailTrace_5559447
  have hstable : (prefixWord ++ tailWord_5559447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559447).length < 2 ^ (prefixWord ++ tailWord_5559447).sum := by decide
  have hdescent : baseEnd_5559447 < baseStart_5559447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559456 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_5559456 : Nat := 118140960795 + 5559456 * 2 ^ 59
def prefixEnd_5559456 : Nat := 4983230072969 + 3 ^ 40 * 5559456 * 2
def baseEnd_5559456 : Nat := 951557701840768612177511

theorem tailTrace_5559456 : CollatzResearch.WordTrace tailWord_5559456 prefixEnd_5559456 951557701840768612177511 := by
  unfold tailWord_5559456
  simp only [CollatzResearch.WordTrace]
  refine ⟨101385009273523933168993111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135180012364698577558657481 101385009273523933168993111)
  ·
    refine ⟨152077513910285899753489667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101385009273523933168993111 152077513910285899753489667)
    ·
      refine ⟨228116270865428849630234501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152077513910285899753489667 228116270865428849630234501)
      ·
        refine ⟨42771800787267909305668969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228116270865428849630234501 42771800787267909305668969)
        ·
          refine ⟨32078850590450931979251727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42771800787267909305668969 32078850590450931979251727)
          ·
            refine ⟨48118275885676397968877591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32078850590450931979251727 48118275885676397968877591)
            ·
              refine ⟨72177413828514596953316387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48118275885676397968877591 72177413828514596953316387)
              ·
                refine ⟨108266120742771895429974581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72177413828514596953316387 108266120742771895429974581)
                ·
                  refine ⟨10149948819634865196560117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108266120742771895429974581 10149948819634865196560117)
                  ·
                    refine ⟨951557701840768612177511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10149948819634865196560117 951557701840768612177511)
                    ·
                      rfl

theorem cell23_5559456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_5559456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559456 prefixEnd_5559456 := by exact prefixLift 5559456
  have htrace : WordTrace (prefixWord ++ tailWord_5559456) baseStart_5559456 baseEnd_5559456 := by
    simpa [prefixWord, tailWord_5559456, baseEnd_5559456] using wordTrace_append hprefix tailTrace_5559456
  have hstable : (prefixWord ++ tailWord_5559456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559456).length < 2 ^ (prefixWord ++ tailWord_5559456).sum := by decide
  have hdescent : baseEnd_5559456 < baseStart_5559456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559473 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_5559473 : Nat := 118140960795 + 5559473 * 2 ^ 59
def prefixEnd_5559473 : Nat := 4983230072969 + 3 ^ 40 * 5559473 * 2
def baseEnd_5559473 : Nat := 951560611564477423339985

theorem tailTrace_5559473 : CollatzResearch.WordTrace tailWord_5559473 prefixEnd_5559473 951560611564477423339985 := by
  unfold tailWord_5559473
  simp only [CollatzResearch.WordTrace]
  refine ⟨202770638587986278241355073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135180425725324185494236715 202770638587986278241355073)
  ·
    refine ⟨152077978940989708681016305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202770638587986278241355073 152077978940989708681016305)
    ·
      refine ⟨114058484205742281510762229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152077978940989708681016305 114058484205742281510762229)
      ·
        refine ⟨10692982894288338891633959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114058484205742281510762229 10692982894288338891633959)
        ·
          refine ⟨16039474341432508337450939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692982894288338891633959 16039474341432508337450939)
          ·
            refine ⟨24059211512148762506176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16039474341432508337450939 24059211512148762506176409)
            ·
              refine ⟨18044408634111571879632307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24059211512148762506176409 18044408634111571879632307)
              ·
                refine ⟨27066612951167357819448461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18044408634111571879632307 27066612951167357819448461)
                ·
                  refine ⟨10149979856687759182293173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27066612951167357819448461 10149979856687759182293173)
                  ·
                    refine ⟨951560611564477423339985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10149979856687759182293173 951560611564477423339985)
                    ·
                      rfl

theorem cell23_5559473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_5559473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559473 prefixEnd_5559473 := by exact prefixLift 5559473
  have htrace : WordTrace (prefixWord ++ tailWord_5559473) baseStart_5559473 baseEnd_5559473 := by
    simpa [prefixWord, tailWord_5559473, baseEnd_5559473] using wordTrace_append hprefix tailTrace_5559473
  have hstable : (prefixWord ++ tailWord_5559473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559473).length < 2 ^ (prefixWord ++ tailWord_5559473).sum := by decide
  have hdescent : baseEnd_5559473 < baseStart_5559473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559503 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 2, 4]
def baseStart_5559503 : Nat := 118140960795 + 5559503 * 2 ^ 59
def prefixEnd_5559503 : Nat := 4983230072969 + 3 ^ 40 * 5559503 * 2
def baseEnd_5559503 : Nat := 951565746371022384214939

theorem tailTrace_5559503 : CollatzResearch.WordTrace tailWord_5559503 prefixEnd_5559503 951565746371022384214939 := by
  unfold tailWord_5559503
  simp only [CollatzResearch.WordTrace]
  refine ⟨202771732777877593364947163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135181155185251728909964775 202771732777877593364947163)
  ·
    refine ⟨304157599166816390047420745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202771732777877593364947163 304157599166816390047420745)
    ·
      refine ⟨228118199375112292535565559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304157599166816390047420745 228118199375112292535565559)
      ·
        refine ⟨342177299062668438803348339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228118199375112292535565559 342177299062668438803348339)
        ·
          refine ⟨513265948594002658205022509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342177299062668438803348339 513265948594002658205022509)
          ·
            refine ⟨192474730722750996826883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513265948594002658205022509 192474730722750996826883441)
            ·
              refine ⟨144356048042063247620162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192474730722750996826883441 144356048042063247620162581)
              ·
                refine ⟨6766689751971714732195121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144356048042063247620162581 6766689751971714732195121)
                ·
                  refine ⟨5075017313978786049146341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6766689751971714732195121 5075017313978786049146341)
                  ·
                    refine ⟨951565746371022384214939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075017313978786049146341 951565746371022384214939)
                    ·
                      rfl

theorem cell23_5559503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_5559503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559503 prefixEnd_5559503 := by exact prefixLift 5559503
  have htrace : WordTrace (prefixWord ++ tailWord_5559503) baseStart_5559503 baseEnd_5559503 := by
    simpa [prefixWord, tailWord_5559503, baseEnd_5559503] using wordTrace_append hprefix tailTrace_5559503
  have hstable : (prefixWord ++ tailWord_5559503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559503).length < 2 ^ (prefixWord ++ tailWord_5559503).sum := by decide
  have hdescent : baseEnd_5559503 < baseStart_5559503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559527 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5559527 : Nat := 118140960795 + 5559527 * 2 ^ 59
def prefixEnd_5559527 : Nat := 4983230072969 + 3 ^ 40 * 5559527 * 2
def baseEnd_5559527 : Nat := 2854709562648775058744707

theorem tailTrace_5559527 : CollatzResearch.WordTrace tailWord_5559527 prefixEnd_5559527 2854709562648775058744707 := by
  unfold tailWord_5559527
  simp only [CollatzResearch.WordTrace]
  refine ⟨202772608129790645463820835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135181738753193763642547223 202772608129790645463820835)
  ·
    refine ⟨304158912194685968195731253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202772608129790645463820835 304158912194685968195731253)
    ·
      refine ⟨28514898018251809518349805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304158912194685968195731253 28514898018251809518349805)
      ·
        refine ⟨10693086756844428569381177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28514898018251809518349805 10693086756844428569381177)
        ·
          refine ⟨8019815067633321427035883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10693086756844428569381177 8019815067633321427035883)
          ·
            refine ⟨12029722601449982140553825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019815067633321427035883 12029722601449982140553825)
            ·
              refine ⟨9022291951087486605415369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12029722601449982140553825 9022291951087486605415369)
              ·
                refine ⟨6766718963315614954061527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9022291951087486605415369 6766718963315614954061527)
                ·
                  refine ⟨10150078444973422431092291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766718963315614954061527 10150078444973422431092291)
                  ·
                    refine ⟨15225117667460133646638437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10150078444973422431092291 15225117667460133646638437)
                    ·
                      refine ⟨2854709562648775058744707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15225117667460133646638437 2854709562648775058744707)
                      ·
                        rfl

theorem cell23_5559527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5559527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559527 prefixEnd_5559527 := by exact prefixLift 5559527
  have htrace : WordTrace (prefixWord ++ tailWord_5559527) baseStart_5559527 baseEnd_5559527 := by
    simpa [prefixWord, tailWord_5559527, baseEnd_5559527] using wordTrace_append hprefix tailTrace_5559527
  have hstable : (prefixWord ++ tailWord_5559527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559527).length < 2 ^ (prefixWord ++ tailWord_5559527).sum := by decide
  have hdescent : baseEnd_5559527 < baseStart_5559527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559530 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_5559530 : Nat := 118140960795 + 5559530 * 2 ^ 59
def prefixEnd_5559530 : Nat := 4983230072969 + 3 ^ 40 * 5559530 * 2
def baseEnd_5559530 : Nat := 2854711103090738547007193

theorem tailTrace_5559530 : CollatzResearch.WordTrace tailWord_5559530 prefixEnd_5559530 2854711103090738547007193 := by
  unfold tailWord_5559530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50693179387194944244045011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135181811699186517984120029 50693179387194944244045011)
  ·
    refine ⟨76039769080792416366067517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50693179387194944244045011 76039769080792416366067517)
    ·
      refine ⟨28514913405297156137275319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76039769080792416366067517 28514913405297156137275319)
      ·
        refine ⟨42772370107945734205912979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28514913405297156137275319 42772370107945734205912979)
        ·
          refine ⟨64158555161918601308869469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42772370107945734205912979 64158555161918601308869469)
          ·
            refine ⟨24059458185719475490826051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64158555161918601308869469 24059458185719475490826051)
            ·
              refine ⟨36089187278579213236239077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24059458185719475490826051 36089187278579213236239077)
              ·
                refine ⟨6766722614733602481794827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36089187278579213236239077 6766722614733602481794827)
                ·
                  refine ⟨10150083922100403722692241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766722614733602481794827 10150083922100403722692241)
                  ·
                    refine ⟨7612562941575302792019181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10150083922100403722692241 7612562941575302792019181)
                    ·
                      refine ⟨2854711103090738547007193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612562941575302792019181 2854711103090738547007193)
                      ·
                        rfl

theorem cell23_5559530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_5559530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559530 prefixEnd_5559530 := by exact prefixLift 5559530
  have htrace : WordTrace (prefixWord ++ tailWord_5559530) baseStart_5559530 baseEnd_5559530 := by
    simpa [prefixWord, tailWord_5559530, baseEnd_5559530] using wordTrace_append hprefix tailTrace_5559530
  have hstable : (prefixWord ++ tailWord_5559530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559530).length < 2 ^ (prefixWord ++ tailWord_5559530).sum := by decide
  have hdescent : baseEnd_5559530 < baseStart_5559530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559533 : List Nat := [1, 5, 1, 2, 2, 2, 1, 9]
def baseStart_5559533 : Nat := 118140960795 + 5559533 * 2 ^ 59
def prefixEnd_5559533 : Nat := 4983230072969 + 3 ^ 40 * 5559533 * 2
def baseEnd_5559533 : Nat := 105730097908618593898877

theorem tailTrace_5559533 : CollatzResearch.WordTrace tailWord_5559533 prefixEnd_5559533 105730097908618593898877 := by
  unfold tailWord_5559533
  simp only [CollatzResearch.WordTrace]
  refine ⟨202772826967768908488539253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135181884645179272325692835 202772826967768908488539253)
  ·
    refine ⟨19009952528228335170800555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202772826967768908488539253 19009952528228335170800555)
    ·
      refine ⟨28514928792342502756200833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19009952528228335170800555 28514928792342502756200833)
      ·
        refine ⟨21386196594256877067150625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28514928792342502756200833 21386196594256877067150625)
        ·
          refine ⟨16039647445692657800362969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21386196594256877067150625 16039647445692657800362969)
          ·
            refine ⟨12029735584269493350272227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16039647445692657800362969 12029735584269493350272227)
            ·
              refine ⟨18044603376404240025408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029735584269493350272227 18044603376404240025408341)
              ·
                refine ⟨105730097908618593898877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18044603376404240025408341 105730097908618593898877)
                ·
                  rfl

theorem cell23_5559533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 9].length) (baseStart_5559533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559533 prefixEnd_5559533 := by exact prefixLift 5559533
  have htrace : WordTrace (prefixWord ++ tailWord_5559533) baseStart_5559533 baseEnd_5559533 := by
    simpa [prefixWord, tailWord_5559533, baseEnd_5559533] using wordTrace_append hprefix tailTrace_5559533
  have hstable : (prefixWord ++ tailWord_5559533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559533).length < 2 ^ (prefixWord ++ tailWord_5559533).sum := by decide
  have hdescent : baseEnd_5559533 < baseStart_5559533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559587 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 1, 3, 2]
def baseStart_5559587 : Nat := 118140960795 + 5559587 * 2 ^ 59
def prefixEnd_5559587 : Nat := 4983230072969 + 3 ^ 40 * 5559587 * 2
def baseEnd_5559587 : Nat := 2854740371488044823994431

theorem tailTrace_5559587 : CollatzResearch.WordTrace tailWord_5559587 prefixEnd_5559587 2854740371488044823994431 := by
  unfold tailWord_5559587
  simp only [CollatzResearch.WordTrace]
  refine ⟨202774796509573275711005015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135183197673048850474003343 202774796509573275711005015)
  ·
    refine ⟨304162194764359913566507523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202774796509573275711005015 304162194764359913566507523)
    ·
      refine ⟨456243292146539870349761285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304162194764359913566507523 456243292146539870349761285)
      ·
        refine ⟨85545617277476225690580241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 456243292146539870349761285 85545617277476225690580241)
        ·
          refine ⟨64159212958107169267935181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85545617277476225690580241 64159212958107169267935181)
          ·
            refine ⟨24059704859290188475475693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64159212958107169267935181 24059704859290188475475693)
            ·
              refine ⟨9022389322233820678303385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24059704859290188475475693 9022389322233820678303385)
              ·
                refine ⟨6766791991675365508727539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9022389322233820678303385 6766791991675365508727539)
                ·
                  refine ⟨10150187987513048263091309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766791991675365508727539 10150187987513048263091309)
                  ·
                    refine ⟨3806320495317393098659241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10150187987513048263091309 3806320495317393098659241)
                    ·
                      refine ⟨2854740371488044823994431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806320495317393098659241 2854740371488044823994431)
                      ·
                        rfl

theorem cell23_5559587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_5559587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559587 prefixEnd_5559587 := by exact prefixLift 5559587
  have htrace : WordTrace (prefixWord ++ tailWord_5559587) baseStart_5559587 baseEnd_5559587 := by
    simpa [prefixWord, tailWord_5559587, baseEnd_5559587] using wordTrace_append hprefix tailTrace_5559587
  have hstable : (prefixWord ++ tailWord_5559587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559587).length < 2 ^ (prefixWord ++ tailWord_5559587).sum := by decide
  have hdescent : baseEnd_5559587 < baseStart_5559587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559600 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2]
def baseStart_5559600 : Nat := 118140960795 + 5559600 * 2 ^ 59
def prefixEnd_5559600 : Nat := 4983230072969 + 3 ^ 40 * 5559600 * 2
def baseEnd_5559600 : Nat := 2854747046736553273131871

theorem tailTrace_5559600 : CollatzResearch.WordTrace tailWord_5559600 prefixEnd_5559600 2854747046736553273131871 := by
  unfold tailWord_5559600
  simp only [CollatzResearch.WordTrace]
  refine ⟨101387635329263089465614127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135183513772350785954152169 101387635329263089465614127)
  ·
    refine ⟨152081452993894634198421191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101387635329263089465614127 152081452993894634198421191)
    ·
      refine ⟨228122179490841951297631787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152081452993894634198421191 228122179490841951297631787)
      ·
        refine ⟨342183269236262926946447681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228122179490841951297631787 342183269236262926946447681)
        ·
          refine ⟨256637451927197195209835761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342183269236262926946447681 256637451927197195209835761)
          ·
            refine ⟨192478088945397896407376821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256637451927197195209835761 192478088945397896407376821)
            ·
              refine ⟨18044820838631052788191577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192478088945397896407376821 18044820838631052788191577)
              ·
                refine ⟨13533615628973289591143683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18044820838631052788191577 13533615628973289591143683)
                ·
                  refine ⟨20300423443459934386715525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13533615628973289591143683 20300423443459934386715525)
                  ·
                    refine ⟨3806329395648737697509161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20300423443459934386715525 3806329395648737697509161)
                    ·
                      refine ⟨2854747046736553273131871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806329395648737697509161 2854747046736553273131871)
                      ·
                        rfl

theorem cell23_5559600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2].length) (baseStart_5559600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559600 prefixEnd_5559600 := by exact prefixLift 5559600
  have htrace : WordTrace (prefixWord ++ tailWord_5559600) baseStart_5559600 baseEnd_5559600 := by
    simpa [prefixWord, tailWord_5559600, baseEnd_5559600] using wordTrace_append hprefix tailTrace_5559600
  have hstable : (prefixWord ++ tailWord_5559600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559600).length < 2 ^ (prefixWord ++ tailWord_5559600).sum := by decide
  have hdescent : baseEnd_5559600 < baseStart_5559600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559603 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_5559603 : Nat := 118140960795 + 5559603 * 2 ^ 59
def prefixEnd_5559603 : Nat := 4983230072969 + 3 ^ 40 * 5559603 * 2
def baseEnd_5559603 : Nat := 2854748587178516761394357

theorem tailTrace_5559603 : CollatzResearch.WordTrace tailWord_5559603 prefixEnd_5559603 2854748587178516761394357 := by
  unfold tailWord_5559603
  simp only [CollatzResearch.WordTrace]
  refine ⟨202775380077515310443587463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135183586718343540295724975 202775380077515310443587463)
  ·
    refine ⟨304163070116272965665381195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202775380077515310443587463 304163070116272965665381195)
    ·
      refine ⟨456244605174409448498071793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304163070116272965665381195 456244605174409448498071793)
      ·
        refine ⟨342183453880807086373553845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456244605174409448498071793 342183453880807086373553845)
        ·
          refine ⟨32079698801325664347520673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342183453880807086373553845 32079698801325664347520673)
          ·
            refine ⟨24059774100994248260640505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32079698801325664347520673 24059774100994248260640505)
            ·
              refine ⟨18044830575745686195480379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24059774100994248260640505 18044830575745686195480379)
              ·
                refine ⟨27067245863618529293220569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18044830575745686195480379 27067245863618529293220569)
                ·
                  refine ⟨20300434397713896969915427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27067245863618529293220569 20300434397713896969915427)
                  ·
                    refine ⟨30450651596570845454873141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20300434397713896969915427 30450651596570845454873141)
                    ·
                      refine ⟨2854748587178516761394357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30450651596570845454873141 2854748587178516761394357)
                      ·
                        rfl

theorem cell23_5559603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_5559603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559603 prefixEnd_5559603 := by exact prefixLift 5559603
  have htrace : WordTrace (prefixWord ++ tailWord_5559603) baseStart_5559603 baseEnd_5559603 := by
    simpa [prefixWord, tailWord_5559603, baseEnd_5559603] using wordTrace_append hprefix tailTrace_5559603
  have hstable : (prefixWord ++ tailWord_5559603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559603).length < 2 ^ (prefixWord ++ tailWord_5559603).sum := by decide
  have hdescent : baseEnd_5559603 < baseStart_5559603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559650 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5559650 : Nat := 118140960795 + 5559650 * 2 ^ 59
def prefixEnd_5559650 : Nat := 4983230072969 + 3 ^ 40 * 5559650 * 2
def baseEnd_5559650 : Nat := 2854772720769278077506641

theorem tailTrace_5559650 : CollatzResearch.WordTrace tailWord_5559650 prefixEnd_5559650 2854772720769278077506641 := by
  unfold tailWord_5559650
  simp only [CollatzResearch.WordTrace]
  refine ⟨50694273577086259367637101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135184729538896691647032269 50694273577086259367637101)
  ·
    refine ⟨19010352591407347262863913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50694273577086259367637101 19010352591407347262863913)
    ·
      refine ⟨14257764443555510447147935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19010352591407347262863913 14257764443555510447147935)
      ·
        refine ⟨21386646665333265670721903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14257764443555510447147935 21386646665333265670721903)
        ·
          refine ⟨32079969997999898506082855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21386646665333265670721903 32079969997999898506082855)
          ·
            refine ⟨48119954996999847759124283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32079969997999898506082855 48119954996999847759124283)
            ·
              refine ⟨72179932495499771638686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48119954996999847759124283 72179932495499771638686425)
              ·
                refine ⟨54134949371624828729014819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72179932495499771638686425 54134949371624828729014819)
                ·
                  refine ⟨81202424057437243093522229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54134949371624828729014819 81202424057437243093522229)
                  ·
                    refine ⟨7612727255384741540017709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81202424057437243093522229 7612727255384741540017709)
                    ·
                      refine ⟨2854772720769278077506641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612727255384741540017709 2854772720769278077506641)
                      ·
                        rfl

theorem cell23_5559650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5559650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559650 prefixEnd_5559650 := by exact prefixLift 5559650
  have htrace : WordTrace (prefixWord ++ tailWord_5559650) baseStart_5559650 baseEnd_5559650 := by
    simpa [prefixWord, tailWord_5559650, baseEnd_5559650] using wordTrace_append hprefix tailTrace_5559650
  have hstable : (prefixWord ++ tailWord_5559650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559650).length < 2 ^ (prefixWord ++ tailWord_5559650).sum := by decide
  have hdescent : baseEnd_5559650 < baseStart_5559650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559653 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_5559653 : Nat := 118140960795 + 5559653 * 2 ^ 59
def prefixEnd_5559653 : Nat := 4983230072969 + 3 ^ 40 * 5559653 * 2
def baseEnd_5559653 : Nat := 951591420403747188589709

theorem tailTrace_5559653 : CollatzResearch.WordTrace tailWord_5559653 prefixEnd_5559653 951591420403747188589709 := by
  unfold tailWord_5559653
  simp only [CollatzResearch.WordTrace]
  refine ⟨202777203727334168982907613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135184802484889445988605075 202777203727334168982907613)
  ·
    refine ⟨76041451397750313368590355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202777203727334168982907613 76041451397750313368590355)
    ·
      refine ⟨114062177096625470052885533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76041451397750313368590355 114062177096625470052885533)
      ·
        refine ⟨42773316411234551269832075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114062177096625470052885533 42773316411234551269832075)
        ·
          refine ⟨64159974616851826904748113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42773316411234551269832075 64159974616851826904748113)
          ·
            refine ⟨48119980962638870178561085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64159974616851826904748113 48119980962638870178561085)
            ·
              refine ⟨18044992860989576316960407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48119980962638870178561085 18044992860989576316960407)
              ·
                refine ⟨27067489291484364475440611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18044992860989576316960407 27067489291484364475440611)
                ·
                  refine ⟨40601233937226546713160917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27067489291484364475440611 40601233937226546713160917)
                  ·
                    refine ⟨951591420403747188589709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40601233937226546713160917 951591420403747188589709)
                    ·
                      rfl

theorem cell23_5559653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_5559653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559653 prefixEnd_5559653 := by exact prefixLift 5559653
  have htrace : WordTrace (prefixWord ++ tailWord_5559653) baseStart_5559653 baseEnd_5559653 := by
    simpa [prefixWord, tailWord_5559653, baseEnd_5559653] using wordTrace_append hprefix tailTrace_5559653
  have hstable : (prefixWord ++ tailWord_5559653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559653).length < 2 ^ (prefixWord ++ tailWord_5559653).sum := by decide
  have hdescent : baseEnd_5559653 < baseStart_5559653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559703 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5559703 : Nat := 118140960795 + 5559703 * 2 ^ 59
def prefixEnd_5559703 : Nat := 4983230072969 + 3 ^ 40 * 5559703 * 2
def baseEnd_5559703 : Nat := 2854799935243966370143897

theorem tailTrace_5559703 : CollatzResearch.WordTrace tailWord_5559703 prefixEnd_5559703 2854799935243966370143897 := by
  unfold tailWord_5559703
  simp only [CollatzResearch.WordTrace]
  refine ⟨202779027377153027522227763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135186018251435351681485175 202779027377153027522227763)
  ·
    refine ⟨304168541065729541283341645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202779027377153027522227763 304168541065729541283341645)
    ·
      refine ⟨114063202899648577981253117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304168541065729541283341645 114063202899648577981253117)
      ·
        refine ⟨42773701087368216742969919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114063202899648577981253117 42773701087368216742969919)
        ·
          refine ⟨64160551631052325114454879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42773701087368216742969919 64160551631052325114454879)
          ·
            refine ⟨96240827446578487671682319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64160551631052325114454879 96240827446578487671682319)
            ·
              refine ⟨144361241169867731507523479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96240827446578487671682319 144361241169867731507523479)
              ·
                refine ⟨216541861754801597261285219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144361241169867731507523479 216541861754801597261285219)
                ·
                  refine ⟨324812792632202395891927829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216541861754801597261285219 324812792632202395891927829)
                  ·
                    refine ⟨15225599654634487307434117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 324812792632202395891927829 15225599654634487307434117)
                    ·
                      refine ⟨2854799935243966370143897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15225599654634487307434117 2854799935243966370143897)
                      ·
                        rfl

theorem cell23_5559703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5559703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559703 prefixEnd_5559703 := by exact prefixLift 5559703
  have htrace : WordTrace (prefixWord ++ tailWord_5559703) baseStart_5559703 baseEnd_5559703 := by
    simpa [prefixWord, tailWord_5559703, baseEnd_5559703] using wordTrace_append hprefix tailTrace_5559703
  have hstable : (prefixWord ++ tailWord_5559703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559703).length < 2 ^ (prefixWord ++ tailWord_5559703).sum := by decide
  have hdescent : baseEnd_5559703 < baseStart_5559703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559717 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_5559717 : Nat := 118140960795 + 5559717 * 2 ^ 59
def prefixEnd_5559717 : Nat := 4983230072969 + 3 ^ 40 * 5559717 * 2
def baseEnd_5559717 : Nat := 951602374657709771789611

theorem tailTrace_5559717 : CollatzResearch.WordTrace tailWord_5559717 prefixEnd_5559717 951602374657709771789611 := by
  unfold tailWord_5559717
  simp only [CollatzResearch.WordTrace]
  refine ⟨202779537999102307913237405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135186358666068205275491603 202779537999102307913237405)
  ·
    refine ⟨76042326749663365467464027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202779537999102307913237405 76042326749663365467464027)
    ·
      refine ⟨114063490124495048201196041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76042326749663365467464027 114063490124495048201196041)
      ·
        refine ⟨85547617593371286150897031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114063490124495048201196041 85547617593371286150897031)
        ·
          refine ⟨128321426390056929226345547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85547617593371286150897031 128321426390056929226345547)
          ·
            refine ⟨192482139585085393839518321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128321426390056929226345547 192482139585085393839518321)
            ·
              refine ⟨144361604688814045379638741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192482139585085393839518321 144361604688814045379638741)
              ·
                refine ⟨3383475109894079188585283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144361604688814045379638741 3383475109894079188585283)
                ·
                  refine ⟨5075212664841118782877925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383475109894079188585283 5075212664841118782877925)
                  ·
                    refine ⟨951602374657709771789611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075212664841118782877925 951602374657709771789611)
                    ·
                      rfl

theorem cell23_5559717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_5559717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559717 prefixEnd_5559717 := by exact prefixLift 5559717
  have htrace : WordTrace (prefixWord ++ tailWord_5559717) baseStart_5559717 baseEnd_5559717 := by
    simpa [prefixWord, tailWord_5559717, baseEnd_5559717] using wordTrace_append hprefix tailTrace_5559717
  have hstable : (prefixWord ++ tailWord_5559717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559717).length < 2 ^ (prefixWord ++ tailWord_5559717).sum := by decide
  have hdescent : baseEnd_5559717 < baseStart_5559717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559790 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_5559790 : Nat := 118140960795 + 5559790 * 2 ^ 59
def prefixEnd_5559790 : Nat := 4983230072969 + 3 ^ 40 * 5559790 * 2
def baseEnd_5559790 : Nat := 951614869353635843251999

theorem tailTrace_5559790 : CollatzResearch.WordTrace tailWord_5559790 prefixEnd_5559790 951614869353635843251999 := by
  unfold tailWord_5559790
  simp only [CollatzResearch.WordTrace]
  refine ⟨25347775065979730172580603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135188133685225227587096549 25347775065979730172580603)
  ·
    refine ⟨38021662598969595258870905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25347775065979730172580603 38021662598969595258870905)
    ·
      refine ⟨28516246949227196444153179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38021662598969595258870905 28516246949227196444153179)
      ·
        refine ⟨42774370423840794666229769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28516246949227196444153179 42774370423840794666229769)
        ·
          refine ⟨32080777817880595999672327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42774370423840794666229769 32080777817880595999672327)
          ·
            refine ⟨48121166726820893999508491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32080777817880595999672327 48121166726820893999508491)
            ·
              refine ⟨72181750090231340999262737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48121166726820893999508491 72181750090231340999262737)
              ·
                refine ⟨54136312567673505749447053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72181750090231340999262737 54136312567673505749447053)
                ·
                  refine ⟨20301117212877564656042645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54136312567673505749447053 20301117212877564656042645)
                  ·
                    refine ⟨951614869353635843251999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20301117212877564656042645 951614869353635843251999)
                    ·
                      rfl

theorem cell23_5559790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_5559790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559790 prefixEnd_5559790 := by exact prefixLift 5559790
  have htrace : WordTrace (prefixWord ++ tailWord_5559790) baseStart_5559790 baseEnd_5559790 := by
    simpa [prefixWord, tailWord_5559790, baseEnd_5559790] using wordTrace_append hprefix tailTrace_5559790
  have hstable : (prefixWord ++ tailWord_5559790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559790).length < 2 ^ (prefixWord ++ tailWord_5559790).sum := by decide
  have hdescent : baseEnd_5559790 < baseStart_5559790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559791 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 1, 1, 3]
def baseStart_5559791 : Nat := 118140960795 + 5559791 * 2 ^ 59
def prefixEnd_5559791 : Nat := 4983230072969 + 3 ^ 40 * 5559791 * 2
def baseEnd_5559791 : Nat := 2854845121541562025843493

theorem tailTrace_5559791 : CollatzResearch.WordTrace tailWord_5559791 prefixEnd_5559791 2854845121541562025843493 := by
  unfold tailWord_5559791
  simp only [CollatzResearch.WordTrace]
  refine ⟨202782237000834218551431227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135188158000556145700954151 202782237000834218551431227)
  ·
    refine ⟨304173355501251327827146841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202782237000834218551431227 304173355501251327827146841)
    ·
      refine ⟨228130016625938495870360131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304173355501251327827146841 228130016625938495870360131)
      ·
        refine ⟨342195024938907743805540197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228130016625938495870360131 342195024938907743805540197)
        ·
          refine ⟨64161567176045201963538787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342195024938907743805540197 64161567176045201963538787)
          ·
            refine ⟨96242350764067802945308181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64161567176045201963538787 96242350764067802945308181)
            ·
              refine ⟨4511360192065678263061321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96242350764067802945308181 4511360192065678263061321)
              ·
                refine ⟨3383520144049258697295991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511360192065678263061321 3383520144049258697295991)
                ·
                  refine ⟨5075280216073888045943987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383520144049258697295991 5075280216073888045943987)
                  ·
                    refine ⟨7612920324110832068915981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5075280216073888045943987 7612920324110832068915981)
                    ·
                      refine ⟨2854845121541562025843493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612920324110832068915981 2854845121541562025843493)
                      ·
                        rfl

theorem cell23_5559791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 1, 3].length) (baseStart_5559791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559791 prefixEnd_5559791 := by exact prefixLift 5559791
  have htrace : WordTrace (prefixWord ++ tailWord_5559791) baseStart_5559791 baseEnd_5559791 := by
    simpa [prefixWord, tailWord_5559791, baseEnd_5559791] using wordTrace_append hprefix tailTrace_5559791
  have hstable : (prefixWord ++ tailWord_5559791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559791).length < 2 ^ (prefixWord ++ tailWord_5559791).sum := by decide
  have hdescent : baseEnd_5559791 < baseStart_5559791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559817 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_5559817 : Nat := 118140960795 + 5559817 * 2 ^ 59
def prefixEnd_5559817 : Nat := 4983230072969 + 3 ^ 40 * 5559817 * 2
def baseEnd_5559817 : Nat := 2854858472038578924118373

theorem tailTrace_5559817 : CollatzResearch.WordTrace tailWord_5559817 prefixEnd_5559817 2854858472038578924118373 := by
  unfold tailWord_5559817
  simp only [CollatzResearch.WordTrace]
  refine ⟨202783185298740024991877705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135188790199160016661251803 202783185298740024991877705)
  ·
    refine ⟨152087388974055018743908279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202783185298740024991877705 152087388974055018743908279)
    ·
      refine ⟨228131083461082528115862419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152087388974055018743908279 228131083461082528115862419)
      ·
        refine ⟨342196625191623792173793629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228131083461082528115862419 342196625191623792173793629)
        ·
          refine ⟨128323734446858922065172611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342196625191623792173793629 128323734446858922065172611)
          ·
            refine ⟨192485601670288383097758917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128323734446858922065172611 192485601670288383097758917)
            ·
              refine ⟨36091050313179071830829797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192485601670288383097758917 36091050313179071830829797)
              ·
                refine ⟨6767071933721075968280587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36091050313179071830829797 6767071933721075968280587)
                ·
                  refine ⟨10150607900581613952420881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767071933721075968280587 10150607900581613952420881)
                  ·
                    refine ⟨7612955925436210464315661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10150607900581613952420881 7612955925436210464315661)
                    ·
                      refine ⟨2854858472038578924118373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7612955925436210464315661 2854858472038578924118373)
                      ·
                        rfl

theorem cell23_5559817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_5559817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559817 prefixEnd_5559817 := by exact prefixLift 5559817
  have htrace : WordTrace (prefixWord ++ tailWord_5559817) baseStart_5559817 baseEnd_5559817 := by
    simpa [prefixWord, tailWord_5559817, baseEnd_5559817] using wordTrace_append hprefix tailTrace_5559817
  have hstable : (prefixWord ++ tailWord_5559817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559817).length < 2 ^ (prefixWord ++ tailWord_5559817).sum := by decide
  have hdescent : baseEnd_5559817 < baseStart_5559817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559828 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5559828 : Nat := 118140960795 + 5559828 * 2 ^ 59
def prefixEnd_5559828 : Nat := 4983230072969 + 3 ^ 40 * 5559828 * 2
def baseEnd_5559828 : Nat := 951621373441926127026941

theorem tailTrace_5559828 : CollatzResearch.WordTrace tailWord_5559828 prefixEnd_5559828 951621373441926127026941 := by
  unfold tailWord_5559828
  simp only [CollatzResearch.WordTrace]
  refine ⟨101391793250850086935264069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135189057667800115913685425 101391793250850086935264069)
  ·
    refine ⟨19010961234534391300362013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101391793250850086935264069 19010961234534391300362013)
    ·
      refine ⟨7129110462950396737635755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19010961234534391300362013 7129110462950396737635755)
      ·
        refine ⟨10693665694425595106453633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7129110462950396737635755 10693665694425595106453633)
        ·
          refine ⟨8020249270819196329840225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10693665694425595106453633 8020249270819196329840225)
          ·
            refine ⟨6015186953114397247380169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8020249270819196329840225 6015186953114397247380169)
            ·
              refine ⟨4511390214835797935535127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015186953114397247380169 4511390214835797935535127)
              ·
                refine ⟨6767085322253696903302691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511390214835797935535127 6767085322253696903302691)
                ·
                  refine ⟨10150627983380545354954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767085322253696903302691 10150627983380545354954037)
                  ·
                    refine ⟨951621373441926127026941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10150627983380545354954037 951621373441926127026941)
                    ·
                      rfl

theorem cell23_5559828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5559828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559828 prefixEnd_5559828 := by exact prefixLift 5559828
  have htrace : WordTrace (prefixWord ++ tailWord_5559828) baseStart_5559828 baseEnd_5559828 := by
    simpa [prefixWord, tailWord_5559828, baseEnd_5559828] using wordTrace_append hprefix tailTrace_5559828
  have hstable : (prefixWord ++ tailWord_5559828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559828).length < 2 ^ (prefixWord ++ tailWord_5559828).sum := by decide
  have hdescent : baseEnd_5559828 < baseStart_5559828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559848 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5559848 : Nat := 118140960795 + 5559848 * 2 ^ 59
def prefixEnd_5559848 : Nat := 4983230072969 + 3 ^ 40 * 5559848 * 2
def baseEnd_5559848 : Nat := 2854874389938868302830731

theorem tailTrace_5559848 : CollatzResearch.WordTrace tailWord_5559848 prefixEnd_5559848 2854874389938868302830731 := by
  unfold tailWord_5559848
  simp only [CollatzResearch.WordTrace]
  refine ⟨101392157980813858643128099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135189543974418478190837465 101392157980813858643128099)
  ·
    refine ⟨152088236971220787964692149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101392157980813858643128099 152088236971220787964692149)
    ·
      refine ⟨14258272216051948871689889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152088236971220787964692149 14258272216051948871689889)
      ·
        refine ⟨10693704162038961653767417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14258272216051948871689889 10693704162038961653767417)
        ·
          refine ⟨8020278121529221240325563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10693704162038961653767417 8020278121529221240325563)
          ·
            refine ⟨12030417182293831860488345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020278121529221240325563 12030417182293831860488345)
            ·
              refine ⟨9022812886720373895366259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12030417182293831860488345 9022812886720373895366259)
              ·
                refine ⟨13534219330080560843049389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9022812886720373895366259 13534219330080560843049389)
                ·
                  refine ⟨5075332248780210316143521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13534219330080560843049389 5075332248780210316143521)
                  ·
                    refine ⟨3806499186585157737107641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5075332248780210316143521 3806499186585157737107641)
                    ·
                      refine ⟨2854874389938868302830731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806499186585157737107641 2854874389938868302830731)
                      ·
                        rfl

theorem cell23_5559848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5559848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559848 prefixEnd_5559848 := by exact prefixLift 5559848
  have htrace : WordTrace (prefixWord ++ tailWord_5559848) baseStart_5559848 baseEnd_5559848 := by
    simpa [prefixWord, tailWord_5559848, baseEnd_5559848] using wordTrace_append hprefix tailTrace_5559848
  have hstable : (prefixWord ++ tailWord_5559848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559848).length < 2 ^ (prefixWord ++ tailWord_5559848).sum := by decide
  have hdescent : baseEnd_5559848 < baseStart_5559848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559864 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_5559864 : Nat := 118140960795 + 5559864 * 2 ^ 59
def prefixEnd_5559864 : Nat := 4983230072969 + 3 ^ 40 * 5559864 * 2
def baseEnd_5559864 : Nat := 2854882605629340240230657

theorem tailTrace_5559864 : CollatzResearch.WordTrace tailWord_5559864 prefixEnd_5559864 2854882605629340240230657 := by
  unfold tailWord_5559864
  simp only [CollatzResearch.WordTrace]
  refine ⟨101392449764784876009419323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135189933019713168012559097 101392449764784876009419323)
  ·
    refine ⟨152088674647177314014128985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101392449764784876009419323 152088674647177314014128985)
    ·
      refine ⟨114066505985382985510596739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152088674647177314014128985 114066505985382985510596739)
      ·
        refine ⟨171099758978074478265895109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114066505985382985510596739 171099758978074478265895109)
        ·
          refine ⟨32081204808388964674855333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171099758978074478265895109 32081204808388964674855333)
          ·
            refine ⟨6015225901572930876535375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32081204808388964674855333 6015225901572930876535375)
            ·
              refine ⟨9022838852359396314803063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015225901572930876535375 9022838852359396314803063)
              ·
                refine ⟨13534258278539094472204595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9022838852359396314803063 13534258278539094472204595)
                ·
                  refine ⟨20301387417808641708306893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13534258278539094472204595 20301387417808641708306893)
                  ·
                    refine ⟨7613020281678240640615085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20301387417808641708306893 7613020281678240640615085)
                    ·
                      refine ⟨2854882605629340240230657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7613020281678240640615085 2854882605629340240230657)
                      ·
                        rfl

theorem cell23_5559864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_5559864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559864 prefixEnd_5559864 := by exact prefixLift 5559864
  have htrace : WordTrace (prefixWord ++ tailWord_5559864) baseStart_5559864 baseEnd_5559864 := by
    simpa [prefixWord, tailWord_5559864, baseEnd_5559864] using wordTrace_append hprefix tailTrace_5559864
  have hstable : (prefixWord ++ tailWord_5559864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559864).length < 2 ^ (prefixWord ++ tailWord_5559864).sum := by decide
  have hdescent : baseEnd_5559864 < baseStart_5559864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559887 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 4, 2]
def baseStart_5559887 : Nat := 118140960795 + 5559887 * 2 ^ 59
def prefixEnd_5559887 : Nat := 4983230072969 + 3 ^ 40 * 5559887 * 2
def baseEnd_5559887 : Nat := 2854894415684393650243051

theorem tailTrace_5559887 : CollatzResearch.WordTrace tailWord_5559887 prefixEnd_5559887 2854894415684393650243051 := by
  unfold tailWord_5559887
  simp only [CollatzResearch.WordTrace]
  refine ⟨202785738408486426946925915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135190492272324284631283943 202785738408486426946925915)
  ·
    refine ⟨304178607612729640420388873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202785738408486426946925915 304178607612729640420388873)
    ·
      refine ⟨228133955709547230315291655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304178607612729640420388873 228133955709547230315291655)
      ·
        refine ⟨342200933564320845472937483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228133955709547230315291655 342200933564320845472937483)
        ·
          refine ⟨513301400346481268209406225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342200933564320845472937483 513301400346481268209406225)
          ·
            refine ⟨384976050259860951157054669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513301400346481268209406225 384976050259860951157054669)
            ·
              refine ⟨144366018847447856683895501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384976050259860951157054669 144366018847447856683895501)
              ·
                refine ⟨54137257067792946256460813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144366018847447856683895501 54137257067792946256460813)
                ·
                  refine ⟨20301471400422354846172805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54137257067792946256460813 20301471400422354846172805)
                  ·
                    refine ⟨3806525887579191533657401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20301471400422354846172805 3806525887579191533657401)
                    ·
                      refine ⟨2854894415684393650243051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806525887579191533657401 2854894415684393650243051)
                      ·
                        rfl

theorem cell23_5559887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4, 2].length) (baseStart_5559887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559887 prefixEnd_5559887 := by exact prefixLift 5559887
  have htrace : WordTrace (prefixWord ++ tailWord_5559887) baseStart_5559887 baseEnd_5559887 := by
    simpa [prefixWord, tailWord_5559887, baseEnd_5559887] using wordTrace_append hprefix tailTrace_5559887
  have hstable : (prefixWord ++ tailWord_5559887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559887).length < 2 ^ (prefixWord ++ tailWord_5559887).sum := by decide
  have hdescent : baseEnd_5559887 < baseStart_5559887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5559994 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_5559994 : Nat := 118140960795 + 5559994 * 2 ^ 59
def prefixEnd_5559994 : Nat := 4983230072969 + 3 ^ 40 * 5559994 * 2
def baseEnd_5559994 : Nat := 2854949358114424731605059

theorem tailTrace_5559994 : CollatzResearch.WordTrace tailWord_5559994 prefixEnd_5559994 2854949358114424731605059 := by
  unfold tailWord_5559994
  simp only [CollatzResearch.WordTrace]
  refine ⟨50697410254774696055267759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135193094012732522814047357 50697410254774696055267759)
  ·
    refine ⟨76046115382162044082901639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50697410254774696055267759 76046115382162044082901639)
    ·
      refine ⟨114069173073243066124352459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76046115382162044082901639 114069173073243066124352459)
      ·
        refine ⟨171103759609864599186528689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114069173073243066124352459 171103759609864599186528689)
        ·
          refine ⟨128327819707398449389896517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171103759609864599186528689 128327819707398449389896517)
          ·
            refine ⟨24061466195137209260605597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128327819707398449389896517 24061466195137209260605597)
            ·
              refine ⟨9023049823176453472727099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24061466195137209260605597 9023049823176453472727099)
              ·
                refine ⟨13534574734764680209090649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9023049823176453472727099 13534574734764680209090649)
                ·
                  refine ⟨10150931051073510156817987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13534574734764680209090649 10150931051073510156817987)
                  ·
                    refine ⟨15226396576610265235226981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10150931051073510156817987 15226396576610265235226981)
                    ·
                      refine ⟨2854949358114424731605059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15226396576610265235226981 2854949358114424731605059)
                      ·
                        rfl

theorem cell23_5559994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_5559994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5559994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5559994 prefixEnd_5559994 := by exact prefixLift 5559994
  have htrace : WordTrace (prefixWord ++ tailWord_5559994) baseStart_5559994 baseEnd_5559994 := by
    simpa [prefixWord, tailWord_5559994, baseEnd_5559994] using wordTrace_append hprefix tailTrace_5559994
  have hstable : (prefixWord ++ tailWord_5559994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5559994).length < 2 ^ (prefixWord ++ tailWord_5559994).sum := by decide
  have hdescent : baseEnd_5559994 < baseStart_5559994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5559994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560004 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5560004 : Nat := 118140960795 + 5560004 * 2 ^ 59
def prefixEnd_5560004 : Nat := 4983230072969 + 3 ^ 40 * 5560004 * 2
def baseEnd_5560004 : Nat := 951651497640323230826671

theorem tailTrace_5560004 : CollatzResearch.WordTrace tailWord_5560004 prefixEnd_5560004 951651497640323230826671 := by
  unfold tailWord_5560004
  simp only [CollatzResearch.WordTrace]
  refine ⟨101395002874531277964467533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135193337166041703952623377 101395002874531277964467533)
  ·
    refine ⟨38023126077949229236675325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101395002874531277964467533 38023126077949229236675325)
    ·
      refine ⟨14258672279230960963753247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38023126077949229236675325 14258672279230960963753247)
      ·
        refine ⟨21388008418846441445629871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14258672279230960963753247 21388008418846441445629871)
        ·
          refine ⟨32082012628269662168444807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21388008418846441445629871 32082012628269662168444807)
          ·
            refine ⟨48123018942404493252667211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32082012628269662168444807 48123018942404493252667211)
            ·
              refine ⟨72184528413606739879000817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48123018942404493252667211 72184528413606739879000817)
              ·
                refine ⟨54138396310205054909250613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72184528413606739879000817 54138396310205054909250613)
                ·
                  refine ⟨5075474654081723897742245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54138396310205054909250613 5075474654081723897742245)
                  ·
                    refine ⟨951651497640323230826671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075474654081723897742245 951651497640323230826671)
                    ·
                      rfl

theorem cell23_5560004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5560004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560004 prefixEnd_5560004 := by exact prefixLift 5560004
  have htrace : WordTrace (prefixWord ++ tailWord_5560004) baseStart_5560004 baseEnd_5560004 := by
    simpa [prefixWord, tailWord_5560004, baseEnd_5560004] using wordTrace_append hprefix tailTrace_5560004
  have hstable : (prefixWord ++ tailWord_5560004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560004).length < 2 ^ (prefixWord ++ tailWord_5560004).sum := by decide
  have hdescent : baseEnd_5560004 < baseStart_5560004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560014 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_5560014 : Nat := 118140960795 + 5560014 * 2 ^ 59
def prefixEnd_5560014 : Nat := 4983230072969 + 3 ^ 40 * 5560014 * 2
def baseEnd_5560014 : Nat := 2854959627727514653354967

theorem tailTrace_5560014 : CollatzResearch.WordTrace tailWord_5560014 prefixEnd_5560014 2854959627727514653354967 := by
  unfold tailWord_5560014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348796309878290954599887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135193580319350885091199397 25348796309878290954599887)
  ·
    refine ⟨38023194464817436431899831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25348796309878290954599887 38023194464817436431899831)
    ·
      refine ⟨57034791697226154647849747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38023194464817436431899831 57034791697226154647849747)
      ·
        refine ⟨85552187545839231971774621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57034791697226154647849747 85552187545839231971774621)
        ·
          refine ⟨32082070329689711989415483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85552187545839231971774621 32082070329689711989415483)
          ·
            refine ⟨48123105494534567984123225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32082070329689711989415483 48123105494534567984123225)
            ·
              refine ⟨36092329120900925988092419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48123105494534567984123225 36092329120900925988092419)
              ·
                refine ⟨54138493681351388982138629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36092329120900925988092419 54138493681351388982138629)
                ·
                  refine ⟨10150967565253385434150993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54138493681351388982138629 10150967565253385434150993)
                  ·
                    refine ⟨7613225673940039075613245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10150967565253385434150993 7613225673940039075613245)
                    ·
                      refine ⟨2854959627727514653354967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7613225673940039075613245 2854959627727514653354967)
                      ·
                        rfl

theorem cell23_5560014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_5560014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560014 prefixEnd_5560014 := by exact prefixLift 5560014
  have htrace : WordTrace (prefixWord ++ tailWord_5560014) baseStart_5560014 baseEnd_5560014 := by
    simpa [prefixWord, tailWord_5560014, baseEnd_5560014] using wordTrace_append hprefix tailTrace_5560014
  have hstable : (prefixWord ++ tailWord_5560014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560014).length < 2 ^ (prefixWord ++ tailWord_5560014).sum := by decide
  have hdescent : baseEnd_5560014 < baseStart_5560014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560017 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 8]
def baseStart_5560017 : Nat := 118140960795 + 5560017 * 2 ^ 59
def prefixEnd_5560017 : Nat := 4983230072969 + 3 ^ 40 * 5560017 * 2
def baseEnd_5560017 : Nat := 317217907574386460179717

theorem tailTrace_5560017 : CollatzResearch.WordTrace tailWord_5560017 prefixEnd_5560017 317217907574386460179717 := by
  unfold tailWord_5560017
  simp only [CollatzResearch.WordTrace]
  refine ⟨202790479898015459149158305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135193653265343639432772203 202790479898015459149158305)
  ·
    refine ⟨152092859923511594361868729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202790479898015459149158305 152092859923511594361868729)
    ·
      refine ⟨114069644942633695771401547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152092859923511594361868729 114069644942633695771401547)
      ·
        refine ⟨171104467413950543657102321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114069644942633695771401547 171104467413950543657102321)
        ·
          refine ⟨128328350560462907742826741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171104467413950543657102321 128328350560462907742826741)
          ·
            refine ⟨12030782865043397600890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128328350560462907742826741 12030782865043397600890007)
            ·
              refine ⟨18046174297565096401335011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12030782865043397600890007 18046174297565096401335011)
              ·
                refine ⟨27069261446347644602002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18046174297565096401335011 27069261446347644602002517)
                ·
                  refine ⟨317217907574386460179717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27069261446347644602002517 317217907574386460179717)
                  ·
                    rfl

theorem cell23_5560017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_5560017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560017 prefixEnd_5560017 := by exact prefixLift 5560017
  have htrace : WordTrace (prefixWord ++ tailWord_5560017) baseStart_5560017 baseEnd_5560017 := by
    simpa [prefixWord, tailWord_5560017, baseEnd_5560017] using wordTrace_append hprefix tailTrace_5560017
  have hstable : (prefixWord ++ tailWord_5560017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560017).length < 2 ^ (prefixWord ++ tailWord_5560017).sum := by decide
  have hdescent : baseEnd_5560017 < baseStart_5560017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560037 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5560037 : Nat := 118140960795 + 5560037 * 2 ^ 59
def prefixEnd_5560037 : Nat := 4983230072969 + 3 ^ 40 * 5560037 * 2
def baseEnd_5560037 : Nat := 2854971437782568063367361

theorem tailTrace_5560037 : CollatzResearch.WordTrace tailWord_5560037 prefixEnd_5560037 2854971437782568063367361 := by
  unfold tailWord_5560037
  simp only [CollatzResearch.WordTrace]
  refine ⟨202791209357943002564886365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135194139571962001709924243 202791209357943002564886365)
  ·
    refine ⟨76046703509228625961832387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202791209357943002564886365 76046703509228625961832387)
    ·
      refine ⟨114070055263842938942748581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76046703509228625961832387 114070055263842938942748581)
      ·
        refine ⟨21388135361970551051765359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114070055263842938942748581 21388135361970551051765359)
        ·
          refine ⟨32082203042955826577648039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21388135361970551051765359 32082203042955826577648039)
          ·
            refine ⟨48123304564433739866472059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32082203042955826577648039 48123304564433739866472059)
            ·
              refine ⟨72184956846650609799708089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48123304564433739866472059 72184956846650609799708089)
              ·
                refine ⟨54138717634987957349781067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72184956846650609799708089 54138717634987957349781067)
                ·
                  refine ⟨81208076452481936024671601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54138717634987957349781067 81208076452481936024671601)
                  ·
                    refine ⟨60906057339361452018503701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81208076452481936024671601 60906057339361452018503701)
                    ·
                      refine ⟨2854971437782568063367361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60906057339361452018503701 2854971437782568063367361)
                      ·
                        rfl

theorem cell23_5560037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5560037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560037 prefixEnd_5560037 := by exact prefixLift 5560037
  have htrace : WordTrace (prefixWord ++ tailWord_5560037) baseStart_5560037 baseEnd_5560037 := by
    simpa [prefixWord, tailWord_5560037, baseEnd_5560037] using wordTrace_append hprefix tailTrace_5560037
  have hstable : (prefixWord ++ tailWord_5560037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560037).length < 2 ^ (prefixWord ++ tailWord_5560037).sum := by decide
  have hdescent : baseEnd_5560037 < baseStart_5560037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560078 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5560078 : Nat := 118140960795 + 5560078 * 2 ^ 59
def prefixEnd_5560078 : Nat := 4983230072969 + 3 ^ 40 * 5560078 * 2
def baseEnd_5560078 : Nat := 2854992490489402402954673

theorem tailTrace_5560078 : CollatzResearch.WordTrace tailWord_5560078 prefixEnd_5560078 2854992490489402402954673 := by
  unfold tailWord_5560078
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349088093849308320891111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135195136500529644378085925 25349088093849308320891111)
  ·
    refine ⟨38023632140773962481336667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25349088093849308320891111 38023632140773962481336667)
    ·
      refine ⟨57035448211160943722005001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38023632140773962481336667 57035448211160943722005001)
      ·
        refine ⟨42776586158370707791503751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57035448211160943722005001 42776586158370707791503751)
        ·
          refine ⟨64164879237556061687255627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42776586158370707791503751 64164879237556061687255627)
          ·
            refine ⟨96247318856334092530883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64164879237556061687255627 96247318856334092530883441)
            ·
              refine ⟨72185489142250569398162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96247318856334092530883441 72185489142250569398162581)
              ·
                refine ⟨3383694803542995440538871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72185489142250569398162581 3383694803542995440538871)
                ·
                  refine ⟨5075542205314493160808307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383694803542995440538871 5075542205314493160808307)
                  ·
                    refine ⟨7613313307971739741212461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5075542205314493160808307 7613313307971739741212461)
                    ·
                      refine ⟨2854992490489402402954673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7613313307971739741212461 2854992490489402402954673)
                      ·
                        rfl

theorem cell23_5560078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5560078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560078 prefixEnd_5560078 := by exact prefixLift 5560078
  have htrace : WordTrace (prefixWord ++ tailWord_5560078) baseStart_5560078 baseEnd_5560078 := by
    simpa [prefixWord, tailWord_5560078, baseEnd_5560078] using wordTrace_append hprefix tailTrace_5560078
  have hstable : (prefixWord ++ tailWord_5560078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560078).length < 2 ^ (prefixWord ++ tailWord_5560078).sum := by decide
  have hdescent : baseEnd_5560078 < baseStart_5560078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560101 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_5560101 : Nat := 118140960795 + 5560101 * 2 ^ 59
def prefixEnd_5560101 : Nat := 4983230072969 + 3 ^ 40 * 5560101 * 2
def baseEnd_5560101 : Nat := 2855004300544455812967067

theorem tailTrace_5560101 : CollatzResearch.WordTrace tailWord_5560101 prefixEnd_5560101 2855004300544455812967067 := by
  unfold tailWord_5560101
  simp only [CollatzResearch.WordTrace]
  refine ⟨202793543629711141495216157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135195695753140760996810771 202793543629711141495216157)
  ·
    refine ⟨76047578861141678060706059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202793543629711141495216157 76047578861141678060706059)
    ·
      refine ⟨114071368291712517091059089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76047578861141678060706059 114071368291712517091059089)
      ·
        refine ⟨85553526218784387818294317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114071368291712517091059089 85553526218784387818294317)
        ·
          refine ⟨32082572332044145431860369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85553526218784387818294317 32082572332044145431860369)
          ·
            refine ⟨24061929249033109073895277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32082572332044145431860369 24061929249033109073895277)
            ·
              refine ⟨9023223468387415902710729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24061929249033109073895277 9023223468387415902710729)
              ·
                refine ⟨6767417601290561927033047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023223468387415902710729 6767417601290561927033047)
                ·
                  refine ⟨10151126401935842890549571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767417601290561927033047 10151126401935842890549571)
                  ·
                    refine ⟨15226689602903764335824357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10151126401935842890549571 15226689602903764335824357)
                    ·
                      refine ⟨2855004300544455812967067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15226689602903764335824357 2855004300544455812967067)
                      ·
                        rfl

theorem cell23_5560101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_5560101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560101 prefixEnd_5560101 := by exact prefixLift 5560101
  have htrace : WordTrace (prefixWord ++ tailWord_5560101) baseStart_5560101 baseEnd_5560101 := by
    simpa [prefixWord, tailWord_5560101, baseEnd_5560101] using wordTrace_append hprefix tailTrace_5560101
  have hstable : (prefixWord ++ tailWord_5560101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560101).length < 2 ^ (prefixWord ++ tailWord_5560101).sum := by decide
  have hdescent : baseEnd_5560101 < baseStart_5560101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560114 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5560114 : Nat := 118140960795 + 5560114 * 2 ^ 59
def prefixEnd_5560114 : Nat := 4983230072969 + 3 ^ 40 * 5560114 * 2
def baseEnd_5560114 : Nat := 2855010975792964262104507

theorem tailTrace_5560114 : CollatzResearch.WordTrace tailWord_5560114 prefixEnd_5560114 2855010975792964262104507 := by
  unfold tailWord_5560114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50698504444666011178859849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135196011852442696476959597 50698504444666011178859849)
  ·
    refine ⟨38023878333499508384144887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50698504444666011178859849 38023878333499508384144887)
    ·
      refine ⟨57035817500249262576217331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38023878333499508384144887 57035817500249262576217331)
      ·
        refine ⟨85553726250373893864325997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57035817500249262576217331 85553726250373893864325997)
        ·
          refine ⟨32082647343890210199122249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85553726250373893864325997 32082647343890210199122249)
          ·
            refine ⟨24061985507917657649341687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32082647343890210199122249 24061985507917657649341687)
            ·
              refine ⟨36092978261876486474012531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24061985507917657649341687 36092978261876486474012531)
              ·
                refine ⟨54139467392814729711018797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36092978261876486474012531 54139467392814729711018797)
                ·
                  refine ⟨20302300272305523641632049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54139467392814729711018797 20302300272305523641632049)
                  ·
                    refine ⟨15226725204229142731224037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20302300272305523641632049 15226725204229142731224037)
                    ·
                      refine ⟨2855010975792964262104507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15226725204229142731224037 2855010975792964262104507)
                      ·
                        rfl

theorem cell23_5560114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5560114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560114 prefixEnd_5560114 := by exact prefixLift 5560114
  have htrace : WordTrace (prefixWord ++ tailWord_5560114) baseStart_5560114 baseEnd_5560114 := by
    simpa [prefixWord, tailWord_5560114, baseEnd_5560114] using wordTrace_append hprefix tailTrace_5560114
  have hstable : (prefixWord ++ tailWord_5560114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560114).length < 2 ^ (prefixWord ++ tailWord_5560114).sum := by decide
  have hdescent : baseEnd_5560114 < baseStart_5560114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560137 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_5560137 : Nat := 118140960795 + 5560137 * 2 ^ 59
def prefixEnd_5560137 : Nat := 4983230072969 + 3 ^ 40 * 5560137 * 2
def baseEnd_5560137 : Nat := 951674261949339224038967

theorem tailTrace_5560137 : CollatzResearch.WordTrace tailWord_5560137 prefixEnd_5560137 951674261949339224038967 := by
  unfold tailWord_5560137
  simp only [CollatzResearch.WordTrace]
  refine ⟨202794856657580719643526665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135196571105053813095684443 202794856657580719643526665)
  ·
    refine ⟨152096142493185539732644999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202794856657580719643526665 152096142493185539732644999)
    ·
      refine ⟨228144213739778309598967499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152096142493185539732644999 228144213739778309598967499)
      ·
        refine ⟨342216320609667464398451249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228144213739778309598967499 342216320609667464398451249)
        ·
          refine ⟨256662240457250598298838437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342216320609667464398451249 256662240457250598298838437)
          ·
            refine ⟨48124170085734487181032207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256662240457250598298838437 48124170085734487181032207)
            ·
              refine ⟨72186255128601730771548311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48124170085734487181032207 72186255128601730771548311)
              ·
                refine ⟨108279382692902596157322467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72186255128601730771548311 108279382692902596157322467)
                ·
                  refine ⟨162419074039353894235983701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108279382692902596157322467 162419074039353894235983701)
                  ·
                    refine ⟨951674261949339224038967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162419074039353894235983701 951674261949339224038967)
                    ·
                      rfl

theorem cell23_5560137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_5560137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560137 prefixEnd_5560137 := by exact prefixLift 5560137
  have htrace : WordTrace (prefixWord ++ tailWord_5560137) baseStart_5560137 baseEnd_5560137 := by
    simpa [prefixWord, tailWord_5560137, baseEnd_5560137] using wordTrace_append hprefix tailTrace_5560137
  have hstable : (prefixWord ++ tailWord_5560137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560137).length < 2 ^ (prefixWord ++ tailWord_5560137).sum := by decide
  have hdescent : baseEnd_5560137 < baseStart_5560137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560141 : List Nat := [1, 6, 1, 2, 1, 1, 3, 8]
def baseStart_5560141 : Nat := 118140960795 + 5560141 * 2 ^ 59
def prefixEnd_5560141 : Nat := 4983230072969 + 3 ^ 40 * 5560141 * 2
def baseEnd_5560141 : Nat := 105741660732245765054329

theorem tailTrace_5560141 : CollatzResearch.WordTrace tailWord_5560141 prefixEnd_5560141 105741660732245765054329 := by
  unfold tailWord_5560141
  simp only [CollatzResearch.WordTrace]
  refine ⟨202795002549566228326672277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135196668366377485551114851 202795002549566228326672277)
  ·
    refine ⟨9506015744510916952812763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202795002549566228326672277 9506015744510916952812763)
    ·
      refine ⟨14259023616766375429219145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9506015744510916952812763 14259023616766375429219145)
      ·
        refine ⟨10694267712574781571914359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14259023616766375429219145 10694267712574781571914359)
        ·
          refine ⟨16041401568862172357871539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10694267712574781571914359 16041401568862172357871539)
          ·
            refine ⟨24062102353293258536807309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16041401568862172357871539 24062102353293258536807309)
            ·
              refine ⟨9023288382484971951302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24062102353293258536807309 9023288382484971951302741)
              ·
                refine ⟨105741660732245765054329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9023288382484971951302741 105741660732245765054329)
                ·
                  rfl

theorem cell23_5560141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 8].length) (baseStart_5560141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560141 prefixEnd_5560141 := by exact prefixLift 5560141
  have htrace : WordTrace (prefixWord ++ tailWord_5560141) baseStart_5560141 baseEnd_5560141 := by
    simpa [prefixWord, tailWord_5560141, baseEnd_5560141] using wordTrace_append hprefix tailTrace_5560141
  have hstable : (prefixWord ++ tailWord_5560141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560141).length < 2 ^ (prefixWord ++ tailWord_5560141).sum := by decide
  have hdescent : baseEnd_5560141 < baseStart_5560141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560147 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_5560147 : Nat := 118140960795 + 5560147 * 2 ^ 59
def prefixEnd_5560147 : Nat := 4983230072969 + 3 ^ 40 * 5560147 * 2
def baseEnd_5560147 : Nat := 2855027920654562632991855

theorem tailTrace_5560147 : CollatzResearch.WordTrace tailWord_5560147 prefixEnd_5560147 2855027920654562632991855 := by
  unfold tailWord_5560147
  simp only [CollatzResearch.WordTrace]
  refine ⟨202795221387544491351390695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135196814258362994234260463 202795221387544491351390695)
  ·
    refine ⟨304192832081316737027086043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202795221387544491351390695 304192832081316737027086043)
    ·
      refine ⟨456289248121975105540629065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304192832081316737027086043 456289248121975105540629065)
      ·
        refine ⟨342216936091481329155471799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456289248121975105540629065 342216936091481329155471799)
        ·
          refine ⟨513325404137221993733207699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342216936091481329155471799 513325404137221993733207699)
          ·
            refine ⟨769988106205832990599811549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513325404137221993733207699 769988106205832990599811549)
            ·
              refine ⟨288745539827187371474929331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 769988106205832990599811549 288745539827187371474929331)
              ·
                refine ⟨433118309740781057212393997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288745539827187371474929331 433118309740781057212393997)
                ·
                  refine ⟨162419366152792896454647749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433118309740781057212393997 162419366152792896454647749)
                  ·
                    refine ⟨30453631153648668085246453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162419366152792896454647749 30453631153648668085246453)
                    ·
                      refine ⟨2855027920654562632991855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30453631153648668085246453 2855027920654562632991855)
                      ·
                        rfl

theorem cell23_5560147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_5560147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560147 prefixEnd_5560147 := by exact prefixLift 5560147
  have htrace : WordTrace (prefixWord ++ tailWord_5560147) baseStart_5560147 baseEnd_5560147 := by
    simpa [prefixWord, tailWord_5560147, baseEnd_5560147] using wordTrace_append hprefix tailTrace_5560147
  have hstable : (prefixWord ++ tailWord_5560147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560147).length < 2 ^ (prefixWord ++ tailWord_5560147).sum := by decide
  have hdescent : baseEnd_5560147 < baseStart_5560147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560161 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_5560161 : Nat := 118140960795 + 5560161 * 2 ^ 59
def prefixEnd_5560161 : Nat := 4983230072969 + 3 ^ 40 * 5560161 * 2
def baseEnd_5560161 : Nat := 2855035109383725578216791

theorem tailTrace_5560161 : CollatzResearch.WordTrace tailWord_5560161 prefixEnd_5560161 2855035109383725578216791 := by
  unfold tailWord_5560161
  simp only [CollatzResearch.WordTrace]
  refine ⟨202795732009493771742400337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135197154672995847828266891 202795732009493771742400337)
  ·
    refine ⟨152096799007120328806800253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202795732009493771742400337 152096799007120328806800253)
    ·
      refine ⟨57036299627670123302550095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152096799007120328806800253 57036299627670123302550095)
      ·
        refine ⟨85554449441505184953825143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57036299627670123302550095 85554449441505184953825143)
        ·
          refine ⟨128331674162257777430737715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85554449441505184953825143 128331674162257777430737715)
          ·
            refine ⟨192497511243386666146106573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128331674162257777430737715 192497511243386666146106573)
            ·
              refine ⟨72186566716269999804789965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192497511243386666146106573 72186566716269999804789965)
              ·
                refine ⟨27069962518601249926796237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72186566716269999804789965 27069962518601249926796237)
                ·
                  refine ⟨10151235944475468722548589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27069962518601249926796237 10151235944475468722548589)
                  ·
                    refine ⟨3806713479178300770955721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10151235944475468722548589 3806713479178300770955721)
                    ·
                      refine ⟨2855035109383725578216791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806713479178300770955721 2855035109383725578216791)
                      ·
                        rfl

theorem cell23_5560161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_5560161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560161 prefixEnd_5560161 := by exact prefixLift 5560161
  have htrace : WordTrace (prefixWord ++ tailWord_5560161) baseStart_5560161 baseEnd_5560161 := by
    simpa [prefixWord, tailWord_5560161, baseEnd_5560161] using wordTrace_append hprefix tailTrace_5560161
  have hstable : (prefixWord ++ tailWord_5560161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560161).length < 2 ^ (prefixWord ++ tailWord_5560161).sum := by decide
  have hdescent : baseEnd_5560161 < baseStart_5560161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560202 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5560202 : Nat := 118140960795 + 5560202 * 2 ^ 59
def prefixEnd_5560202 : Nat := 4983230072969 + 3 ^ 40 * 5560202 * 2
def baseEnd_5560202 : Nat := 2855056162090559917804103

theorem tailTrace_5560202 : CollatzResearch.WordTrace tailWord_5560202 prefixEnd_5560202 2855056162090559917804103 := by
  unfold tailWord_5560202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699306850586308936160715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135198151601563490496428573 50699306850586308936160715)
  ·
    refine ⟨76048960275879463404241073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699306850586308936160715 76048960275879463404241073)
    ·
      refine ⟨57036720206909597553180805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76048960275879463404241073 57036720206909597553180805)
      ·
        refine ⟨10694385038795549541221401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57036720206909597553180805 10694385038795549541221401)
        ·
          refine ⟨8020788779096662155916051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694385038795549541221401 8020788779096662155916051)
          ·
            refine ⟨12031183168644993233874077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020788779096662155916051 12031183168644993233874077)
            ·
              refine ⟨4511693688241872462702779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12031183168644993233874077 4511693688241872462702779)
              ·
                refine ⟨6767540532362808694054169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511693688241872462702779 6767540532362808694054169)
                ·
                  refine ⟨5075655399272106520540627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6767540532362808694054169 5075655399272106520540627)
                  ·
                    refine ⟨7613483098908159780810941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5075655399272106520540627 7613483098908159780810941)
                    ·
                      refine ⟨2855056162090559917804103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7613483098908159780810941 2855056162090559917804103)
                      ·
                        rfl

theorem cell23_5560202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5560202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560202 prefixEnd_5560202 := by exact prefixLift 5560202
  have htrace : WordTrace (prefixWord ++ tailWord_5560202) baseStart_5560202 baseEnd_5560202 := by
    simpa [prefixWord, tailWord_5560202, baseEnd_5560202] using wordTrace_append hprefix tailTrace_5560202
  have hstable : (prefixWord ++ tailWord_5560202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560202).length < 2 ^ (prefixWord ++ tailWord_5560202).sum := by decide
  have hdescent : baseEnd_5560202 < baseStart_5560202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560248 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 5]
def baseStart_5560248 : Nat := 118140960795 + 5560248 * 2 ^ 59
def prefixEnd_5560248 : Nat := 4983230072969 + 3 ^ 40 * 5560248 * 2
def baseEnd_5560248 : Nat := 317231086911185193092099

theorem tailTrace_5560248 : CollatzResearch.WordTrace tailWord_5560248 prefixEnd_5560248 317231086911185193092099 := by
  unfold tailWord_5560248
  simp only [CollatzResearch.WordTrace]
  refine ⟨101399452580089292800408699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135199270106785723733878265 101399452580089292800408699)
  ·
    refine ⟨152099178870133939200613049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101399452580089292800408699 152099178870133939200613049)
    ·
      refine ⟨114074384152600454400459787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152099178870133939200613049 114074384152600454400459787)
      ·
        refine ⟨171111576228900681600689681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114074384152600454400459787 171111576228900681600689681)
        ·
          refine ⟨128333682171675511200517261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171111576228900681600689681 128333682171675511200517261)
          ·
            refine ⟨48125130814378316700193973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128333682171675511200517261 48125130814378316700193973)
            ·
              refine ⟨4511731013847967190643185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48125130814378316700193973 4511731013847967190643185)
              ·
                refine ⟨3383798260385975392982389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511731013847967190643185 3383798260385975392982389)
                ·
                  refine ⟨317231086911185193092099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383798260385975392982389 317231086911185193092099)
                  ·
                    rfl

theorem cell23_5560248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 5].length) (baseStart_5560248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560248 prefixEnd_5560248 := by exact prefixLift 5560248
  have htrace : WordTrace (prefixWord ++ tailWord_5560248) baseStart_5560248 baseEnd_5560248 := by
    simpa [prefixWord, tailWord_5560248, baseEnd_5560248] using wordTrace_append hprefix tailTrace_5560248
  have hstable : (prefixWord ++ tailWord_5560248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560248).length < 2 ^ (prefixWord ++ tailWord_5560248).sum := by decide
  have hdescent : baseEnd_5560248 < baseStart_5560248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560298 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_5560298 : Nat := 118140960795 + 5560298 * 2 ^ 59
def prefixEnd_5560298 : Nat := 4983230072969 + 3 ^ 40 * 5560298 * 2
def baseEnd_5560298 : Nat := 2855105456233391542203661

theorem tailTrace_5560298 : CollatzResearch.WordTrace tailWord_5560298 prefixEnd_5560298 2855105456233391542203661 := by
  unfold tailWord_5560298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700182202499361035034387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135200485873331629426758365 50700182202499361035034387)
  ·
    refine ⟨76050273303749041552551581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50700182202499361035034387 76050273303749041552551581)
    ·
      refine ⟨28518852488905890582206843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76050273303749041552551581 28518852488905890582206843)
      ·
        refine ⟨42778278733358835873310265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518852488905890582206843 42778278733358835873310265)
        ·
          refine ⟨32083709050019126904982699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42778278733358835873310265 32083709050019126904982699)
          ·
            refine ⟨48125563575028690357474049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32083709050019126904982699 48125563575028690357474049)
            ·
              refine ⟨36094172681271517768105537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48125563575028690357474049 36094172681271517768105537)
              ·
                refine ⟨27070629510953638326079153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36094172681271517768105537 27070629510953638326079153)
                ·
                  refine ⟨20302972133215228744559365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27070629510953638326079153 20302972133215228744559365)
                  ·
                    refine ⟨3806807274977855389604881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20302972133215228744559365 3806807274977855389604881)
                    ·
                      refine ⟨2855105456233391542203661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806807274977855389604881 2855105456233391542203661)
                      ·
                        rfl

theorem cell23_5560298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_5560298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560298 prefixEnd_5560298 := by exact prefixLift 5560298
  have htrace : WordTrace (prefixWord ++ tailWord_5560298) baseStart_5560298 baseEnd_5560298 := by
    simpa [prefixWord, tailWord_5560298, baseEnd_5560298] using wordTrace_append hprefix tailTrace_5560298
  have hstable : (prefixWord ++ tailWord_5560298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560298).length < 2 ^ (prefixWord ++ tailWord_5560298).sum := by decide
  have hdescent : baseEnd_5560298 < baseStart_5560298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560304 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 8]
def baseStart_5560304 : Nat := 118140960795 + 5560304 * 2 ^ 59
def prefixEnd_5560304 : Nat := 4983230072969 + 3 ^ 40 * 5560304 * 2
def baseEnd_5560304 : Nat := 317234281901924279858737

theorem tailTrace_5560304 : CollatzResearch.WordTrace tailWord_5560304 prefixEnd_5560304 317234281901924279858737 := by
  unfold tailWord_5560304
  simp only [CollatzResearch.WordTrace]
  refine ⟨101400473823987853582427983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135200631765317138109903977 101400473823987853582427983)
  ·
    refine ⟨152100710735981780373641975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101400473823987853582427983 152100710735981780373641975)
    ·
      refine ⟨228151066103972670560462963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152100710735981780373641975 228151066103972670560462963)
      ·
        refine ⟨342226599155959005840694445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228151066103972670560462963 342226599155959005840694445)
        ·
          refine ⟨128334974683484627190260417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342226599155959005840694445 128334974683484627190260417)
          ·
            refine ⟨96251231012613470392695313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128334974683484627190260417 96251231012613470392695313)
            ·
              refine ⟨72188423259460102794521485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96251231012613470392695313 72188423259460102794521485)
              ·
                refine ⟨27070658722297538547945557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72188423259460102794521485 27070658722297538547945557)
                ·
                  refine ⟨317234281901924279858737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27070658722297538547945557 317234281901924279858737)
                  ·
                    rfl

theorem cell23_5560304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_5560304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560304 prefixEnd_5560304 := by exact prefixLift 5560304
  have htrace : WordTrace (prefixWord ++ tailWord_5560304) baseStart_5560304 baseEnd_5560304 := by
    simpa [prefixWord, tailWord_5560304, baseEnd_5560304] using wordTrace_append hprefix tailTrace_5560304
  have hstable : (prefixWord ++ tailWord_5560304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560304).length < 2 ^ (prefixWord ++ tailWord_5560304).sum := by decide
  have hdescent : baseEnd_5560304 < baseStart_5560304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560321 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 6]
def baseStart_5560321 : Nat := 118140960795 + 5560321 * 2 ^ 59
def prefixEnd_5560321 : Nat := 4983230072969 + 3 ^ 40 * 5560321 * 2
def baseEnd_5560321 : Nat := 317235251809827216912895

theorem tailTrace_5560321 : CollatzResearch.WordTrace tailWord_5560321 prefixEnd_5560321 317235251809827216912895 := by
  unfold tailWord_5560321
  simp only [CollatzResearch.WordTrace]
  refine ⟨202801567688914119068224817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135201045125942746045483211 202801567688914119068224817)
  ·
    refine ⟨152101175766685589301168613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202801567688914119068224817 152101175766685589301168613)
    ·
      refine ⟨28518970456253547993969115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152101175766685589301168613 28518970456253547993969115)
      ·
        refine ⟨42778455684380321990953673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518970456253547993969115 42778455684380321990953673)
        ·
          refine ⟨32083841763285241493215255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42778455684380321990953673 32083841763285241493215255)
          ·
            refine ⟨48125762644927862239822883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32083841763285241493215255 48125762644927862239822883)
            ·
              refine ⟨72188643967391793359734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48125762644927862239822883 72188643967391793359734325)
              ·
                refine ⟨6767685371942980627475093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72188643967391793359734325 6767685371942980627475093)
                ·
                  refine ⟨317235251809827216912895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6767685371942980627475093 317235251809827216912895)
                  ·
                    rfl

theorem cell23_5560321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_5560321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560321 prefixEnd_5560321 := by exact prefixLift 5560321
  have htrace : WordTrace (prefixWord ++ tailWord_5560321) baseStart_5560321 baseEnd_5560321 := by
    simpa [prefixWord, tailWord_5560321, baseEnd_5560321] using wordTrace_append hprefix tailTrace_5560321
  have hstable : (prefixWord ++ tailWord_5560321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560321).length < 2 ^ (prefixWord ++ tailWord_5560321).sum := by decide
  have hdescent : baseEnd_5560321 < baseStart_5560321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560371 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4]
def baseStart_5560371 : Nat := 118140960795 + 5560371 * 2 ^ 59
def prefixEnd_5560371 : Nat := 4983230072969 + 3 ^ 40 * 5560371 * 2
def baseEnd_5560371 : Nat := 2855142940321169756590825

theorem tailTrace_5560371 : CollatzResearch.WordTrace tailWord_5560371 prefixEnd_5560371 2855142940321169756590825 := by
  unfold tailWord_5560371
  simp only [CollatzResearch.WordTrace]
  refine ⟨202803391338732977607544967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135202260892488651738363311 202803391338732977607544967)
  ·
    refine ⟨304205087008099466411317451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202803391338732977607544967 304205087008099466411317451)
    ·
      refine ⟨456307630512149199616976177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304205087008099466411317451 456307630512149199616976177)
      ·
        refine ⟨342230722884111899712732133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456307630512149199616976177 342230722884111899712732133)
        ·
          refine ⟨64168260540770981196137275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342230722884111899712732133 64168260540770981196137275)
          ·
            refine ⟨96252390811156471794205913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64168260540770981196137275 96252390811156471794205913)
            ·
              refine ⟨72189293108367353845654435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96252390811156471794205913 72189293108367353845654435)
              ·
                refine ⟨108283939662551030768481653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72189293108367353845654435 108283939662551030768481653)
                ·
                  refine ⟨10151619343364159134545155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108283939662551030768481653 10151619343364159134545155)
                  ·
                    refine ⟨15227429015046238701817733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10151619343364159134545155 15227429015046238701817733)
                    ·
                      refine ⟨2855142940321169756590825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15227429015046238701817733 2855142940321169756590825)
                      ·
                        rfl

theorem cell23_5560371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_5560371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560371 prefixEnd_5560371 := by exact prefixLift 5560371
  have htrace : WordTrace (prefixWord ++ tailWord_5560371) baseStart_5560371 baseEnd_5560371 := by
    simpa [prefixWord, tailWord_5560371, baseEnd_5560371] using wordTrace_append hprefix tailTrace_5560371
  have hstable : (prefixWord ++ tailWord_5560371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560371).length < 2 ^ (prefixWord ++ tailWord_5560371).sum := by decide
  have hdescent : baseEnd_5560371 < baseStart_5560371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560372 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 6]
def baseStart_5560372 : Nat := 118140960795 + 5560372 * 2 ^ 59
def prefixEnd_5560372 : Nat := 4983230072969 + 3 ^ 40 * 5560372 * 2
def baseEnd_5560372 : Nat := 317238161533536028075369

theorem tailTrace_5560372 : CollatzResearch.WordTrace tailWord_5560372 prefixEnd_5560372 317238161533536028075369 := by
  unfold tailWord_5560372
  simp only [CollatzResearch.WordTrace]
  refine ⟨101401713905864677389165685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135202285207819569852220913 101401713905864677389165685)
  ·
    refine ⟨9506410678674813505234283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101401713905864677389165685 9506410678674813505234283)
    ·
      refine ⟨14259616018012220257851425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9506410678674813505234283 14259616018012220257851425)
      ·
        refine ⟨10694712013509165193388569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14259616018012220257851425 10694712013509165193388569)
        ·
          refine ⟨8021034010131873895041427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694712013509165193388569 8021034010131873895041427)
          ·
            refine ⟨12031551015197810842562141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021034010131873895041427 12031551015197810842562141)
            ·
              refine ⟨4511831630699179065960803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12031551015197810842562141 4511831630699179065960803)
              ·
                refine ⟨6767747446048768598941205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511831630699179065960803 6767747446048768598941205)
                ·
                  refine ⟨317238161533536028075369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6767747446048768598941205 317238161533536028075369)
                  ·
                    rfl

theorem cell23_5560372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_5560372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560372 prefixEnd_5560372 := by exact prefixLift 5560372
  have htrace : WordTrace (prefixWord ++ tailWord_5560372) baseStart_5560372 baseEnd_5560372 := by
    simpa [prefixWord, tailWord_5560372, baseEnd_5560372] using wordTrace_append hprefix tailTrace_5560372
  have hstable : (prefixWord ++ tailWord_5560372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560372).length < 2 ^ (prefixWord ++ tailWord_5560372).sum := by decide
  have hdescent : baseEnd_5560372 < baseStart_5560372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560385 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5560385 : Nat := 118140960795 + 5560385 * 2 ^ 59
def prefixEnd_5560385 : Nat := 4983230072969 + 3 ^ 40 * 5560385 * 2
def baseEnd_5560385 : Nat := 951716709683444233938587

theorem tailTrace_5560385 : CollatzResearch.WordTrace tailWord_5560385 prefixEnd_5560385 951716709683444233938587 := by
  unfold tailWord_5560385
  simp only [CollatzResearch.WordTrace]
  refine ⟨202803901960682257998554609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135202601307121505332369739 202803901960682257998554609)
  ·
    refine ⟨152102926470511693498915957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202803901960682257998554609 152102926470511693498915957)
    ·
      refine ⟨14259649356610471265523371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152102926470511693498915957 14259649356610471265523371)
      ·
        refine ⟨21389474034915706898285057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14259649356610471265523371 21389474034915706898285057)
        ·
          refine ⟨16042105526186780173713793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21389474034915706898285057 16042105526186780173713793)
          ·
            refine ⟨12031579144640085130285345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16042105526186780173713793 12031579144640085130285345)
            ·
              refine ⟨9023684358480063847714009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031579144640085130285345 9023684358480063847714009)
              ·
                refine ⟨6767763268860047885785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023684358480063847714009 6767763268860047885785507)
                ·
                  refine ⟨10151644903290071828678261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767763268860047885785507 10151644903290071828678261)
                  ·
                    refine ⟨951716709683444233938587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10151644903290071828678261 951716709683444233938587)
                    ·
                      rfl

theorem cell23_5560385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5560385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560385 prefixEnd_5560385 := by exact prefixLift 5560385
  have htrace : WordTrace (prefixWord ++ tailWord_5560385) baseStart_5560385 baseEnd_5560385 := by
    simpa [prefixWord, tailWord_5560385, baseEnd_5560385] using wordTrace_append hprefix tailTrace_5560385
  have hstable : (prefixWord ++ tailWord_5560385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560385).length < 2 ^ (prefixWord ++ tailWord_5560385).sum := by decide
  have hdescent : baseEnd_5560385 < baseStart_5560385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560391 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5560391 : Nat := 118140960795 + 5560391 * 2 ^ 59
def prefixEnd_5560391 : Nat := 4983230072969 + 3 ^ 40 * 5560391 * 2
def baseEnd_5560391 : Nat := 2855153209934259678340733

theorem tailTrace_5560391 : CollatzResearch.WordTrace tailWord_5560391 prefixEnd_5560391 2855153209934259678340733 := by
  unfold tailWord_5560391
  simp only [CollatzResearch.WordTrace]
  refine ⟨202804120798660521023273027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135202747199107014015515351 202804120798660521023273027)
  ·
    refine ⟨304206181197990781534909541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202804120798660521023273027 304206181197990781534909541)
    ·
      refine ⟨57038658974623271537795539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304206181197990781534909541 57038658974623271537795539)
      ·
        refine ⟨85557988461934907306693309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57038658974623271537795539 85557988461934907306693309)
        ·
          refine ⟨32084245673225590240009991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85557988461934907306693309 32084245673225590240009991)
          ·
            refine ⟨48126368509838385360014987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32084245673225590240009991 48126368509838385360014987)
            ·
              refine ⟨72189552764757578040022481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48126368509838385360014987 72189552764757578040022481)
              ·
                refine ⟨54142164573568183530016861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72189552764757578040022481 54142164573568183530016861)
                ·
                  refine ⟨20303311715088068823756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54142164573568183530016861 20303311715088068823756323)
                  ·
                    refine ⟨30454967572632103235634485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20303311715088068823756323 30454967572632103235634485)
                    ·
                      refine ⟨2855153209934259678340733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30454967572632103235634485 2855153209934259678340733)
                      ·
                        rfl

theorem cell23_5560391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5560391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560391 prefixEnd_5560391 := by exact prefixLift 5560391
  have htrace : WordTrace (prefixWord ++ tailWord_5560391) baseStart_5560391 baseEnd_5560391 := by
    simpa [prefixWord, tailWord_5560391, baseEnd_5560391] using wordTrace_append hprefix tailTrace_5560391
  have hstable : (prefixWord ++ tailWord_5560391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560391).length < 2 ^ (prefixWord ++ tailWord_5560391).sum := by decide
  have hdescent : baseEnd_5560391 < baseStart_5560391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560398 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_5560398 : Nat := 118140960795 + 5560398 * 2 ^ 59
def prefixEnd_5560398 : Nat := 4983230072969 + 3 ^ 40 * 5560398 * 2
def baseEnd_5560398 : Nat := 951718934766280383651067

theorem tailTrace_5560398 : CollatzResearch.WordTrace tailWord_5560398 prefixEnd_5560398 951718934766280383651067 := by
  unfold tailWord_5560398
  simp only [CollatzResearch.WordTrace]
  refine ⟨25350547013704395152347231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135202917406423440812518565 25350547013704395152347231)
  ·
    refine ⟨38025820520556592728520847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25350547013704395152347231 38025820520556592728520847)
    ·
      refine ⟨57038730780834889092781271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38025820520556592728520847 57038730780834889092781271)
      ·
        refine ⟨85558096171252333639171907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57038730780834889092781271 85558096171252333639171907)
        ·
          refine ⟨128337144256878500458757861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85558096171252333639171907 128337144256878500458757861)
          ·
            refine ⟨24063214548164718836017099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128337144256878500458757861 24063214548164718836017099)
            ·
              refine ⟨36094821822247078254025649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24063214548164718836017099 36094821822247078254025649)
              ·
                refine ⟨27071116366685308690519237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36094821822247078254025649 27071116366685308690519237)
                ·
                  refine ⟨5075834318753495379472357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27071116366685308690519237 5075834318753495379472357)
                  ·
                    refine ⟨951718934766280383651067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075834318753495379472357 951718934766280383651067)
                    ·
                      rfl

theorem cell23_5560398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_5560398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560398 prefixEnd_5560398 := by exact prefixLift 5560398
  have htrace : WordTrace (prefixWord ++ tailWord_5560398) baseStart_5560398 baseEnd_5560398 := by
    simpa [prefixWord, tailWord_5560398, baseEnd_5560398] using wordTrace_append hprefix tailTrace_5560398
  have hstable : (prefixWord ++ tailWord_5560398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560398).length < 2 ^ (prefixWord ++ tailWord_5560398).sum := by decide
  have hdescent : baseEnd_5560398 < baseStart_5560398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560401 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_5560401 : Nat := 118140960795 + 5560401 * 2 ^ 59
def prefixEnd_5560401 : Nat := 4983230072969 + 3 ^ 40 * 5560401 * 2
def baseEnd_5560401 : Nat := 2855158344740804639215687

theorem tailTrace_5560401 : CollatzResearch.WordTrace tailWord_5560401 prefixEnd_5560401 2855158344740804639215687 := by
  unfold tailWord_5560401
  simp only [CollatzResearch.WordTrace]
  refine ⟨202804485528624292731137057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135202990352416195154091371 202804485528624292731137057)
  ·
    refine ⟨152103364146468219548352793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202804485528624292731137057 152103364146468219548352793)
    ·
      refine ⟨114077523109851164661264595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152103364146468219548352793 114077523109851164661264595)
      ·
        refine ⟨171116284664776746991896893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114077523109851164661264595 171116284664776746991896893)
        ·
          refine ⟨64168606749291280121961335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171116284664776746991896893 64168606749291280121961335)
          ·
            refine ⟨96252910123936920182942003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64168606749291280121961335 96252910123936920182942003)
            ·
              refine ⟨144379365185905380274413005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96252910123936920182942003 144379365185905380274413005)
              ·
                refine ⟨54142261944714517602904877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144379365185905380274413005 54142261944714517602904877)
                ·
                  refine ⟨20303348229267944101089329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54142261944714517602904877 20303348229267944101089329)
                  ·
                    refine ⟨15227511171950958075816997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20303348229267944101089329 15227511171950958075816997)
                    ·
                      refine ⟨2855158344740804639215687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15227511171950958075816997 2855158344740804639215687)
                      ·
                        rfl

theorem cell23_5560401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_5560401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560401 prefixEnd_5560401 := by exact prefixLift 5560401
  have htrace : WordTrace (prefixWord ++ tailWord_5560401) baseStart_5560401 baseEnd_5560401 := by
    simpa [prefixWord, tailWord_5560401, baseEnd_5560401] using wordTrace_append hprefix tailTrace_5560401
  have hstable : (prefixWord ++ tailWord_5560401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560401).length < 2 ^ (prefixWord ++ tailWord_5560401).sum := by decide
  have hdescent : baseEnd_5560401 < baseStart_5560401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560408 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_5560408 : Nat := 118140960795 + 5560408 * 2 ^ 59
def prefixEnd_5560408 : Nat := 4983230072969 + 3 ^ 40 * 5560408 * 2
def baseEnd_5560408 : Nat := 2855161939105386111828155

theorem tailTrace_5560408 : CollatzResearch.WordTrace tailWord_5560408 prefixEnd_5560408 2855161939105386111828155 := by
  unfold tailWord_5560408
  simp only [CollatzResearch.WordTrace]
  refine ⟨101402370419799466463320939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135203160559732621951094585 101402370419799466463320939)
  ·
    refine ⟨152103555629699199694981409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101402370419799466463320939 152103555629699199694981409)
    ·
      refine ⟨114077666722274399771236057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152103555629699199694981409 114077666722274399771236057)
      ·
        refine ⟨85558250041705799828427043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114077666722274399771236057 85558250041705799828427043)
        ·
          refine ⟨128337375062558699742640565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85558250041705799828427043 128337375062558699742640565)
          ·
            refine ⟨12031628912114878100872553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128337375062558699742640565 12031628912114878100872553)
            ·
              refine ⟨9023721684086158575654415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031628912114878100872553 9023721684086158575654415)
              ·
                refine ⟨13535582526129237863481623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9023721684086158575654415 13535582526129237863481623)
                ·
                  refine ⟨20303373789193856795222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13535582526129237863481623 20303373789193856795222435)
                  ·
                    refine ⟨30455060683790785192833653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20303373789193856795222435 30455060683790785192833653)
                    ·
                      refine ⟨2855161939105386111828155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30455060683790785192833653 2855161939105386111828155)
                      ·
                        rfl

theorem cell23_5560408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_5560408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560408 prefixEnd_5560408 := by exact prefixLift 5560408
  have htrace : WordTrace (prefixWord ++ tailWord_5560408) baseStart_5560408 baseEnd_5560408 := by
    simpa [prefixWord, tailWord_5560408, baseEnd_5560408] using wordTrace_append hprefix tailTrace_5560408
  have hstable : (prefixWord ++ tailWord_5560408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560408).length < 2 ^ (prefixWord ++ tailWord_5560408).sum := by decide
  have hdescent : baseEnd_5560408 < baseStart_5560408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560432 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_5560432 : Nat := 118140960795 + 5560432 * 2 ^ 59
def prefixEnd_5560432 : Nat := 4983230072969 + 3 ^ 40 * 5560432 * 2
def baseEnd_5560432 : Nat := 951724754213698005976015

theorem tailTrace_5560432 : CollatzResearch.WordTrace tailWord_5560432 prefixEnd_5560432 951724754213698005976015 := by
  unfold tailWord_5560432
  simp only [CollatzResearch.WordTrace]
  refine ⟨101402808095755992512757775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135203744127674656683677033 101402808095755992512757775)
  ·
    refine ⟨152104212143633988769136663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101402808095755992512757775 152104212143633988769136663)
    ·
      refine ⟨228156318215450983153704995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152104212143633988769136663 228156318215450983153704995)
      ·
        refine ⟨342234477323176474730557493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228156318215450983153704995 342234477323176474730557493)
        ·
          refine ⟨32084482249047794505989765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342234477323176474730557493 32084482249047794505989765)
          ·
            refine ⟨6015840421696461469873081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32084482249047794505989765 6015840421696461469873081)
            ·
              refine ⟨4511880316272346102404811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015840421696461469873081 4511880316272346102404811)
              ·
                refine ⟨6767820474408519153607217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511880316272346102404811 6767820474408519153607217)
                ·
                  refine ⟨5075865355806389365205413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6767820474408519153607217 5075865355806389365205413)
                  ·
                    refine ⟨951724754213698005976015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075865355806389365205413 951724754213698005976015)
                    ·
                      rfl

theorem cell23_5560432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_5560432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560432 prefixEnd_5560432 := by exact prefixLift 5560432
  have htrace : WordTrace (prefixWord ++ tailWord_5560432) baseStart_5560432 baseEnd_5560432 := by
    simpa [prefixWord, tailWord_5560432, baseEnd_5560432] using wordTrace_append hprefix tailTrace_5560432
  have hstable : (prefixWord ++ tailWord_5560432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560432).length < 2 ^ (prefixWord ++ tailWord_5560432).sum := by decide
  have hdescent : baseEnd_5560432 < baseStart_5560432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560482 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5560482 : Nat := 118140960795 + 5560482 * 2 ^ 59
def prefixEnd_5560482 : Nat := 4983230072969 + 3 ^ 40 * 5560482 * 2
def baseEnd_5560482 : Nat := 2855199936673818822302815

theorem tailTrace_5560482 : CollatzResearch.WordTrace tailWord_5560482 prefixEnd_5560482 2855199936673818822302815 := by
  unfold tailWord_5560482
  simp only [CollatzResearch.WordTrace]
  refine ⟨50701859960332710891208925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135204959894220562376557133 50701859960332710891208925)
  ·
    refine ⟨19013197485124766584203347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50701859960332710891208925 19013197485124766584203347)
    ·
      refine ⟨28519796227687149876305021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19013197485124766584203347 28519796227687149876305021)
      ·
        refine ⟨10694923585382681203614383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28519796227687149876305021 10694923585382681203614383)
        ·
          refine ⟨16042385378074021805421575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10694923585382681203614383 16042385378074021805421575)
          ·
            refine ⟨24063578067111032708132363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16042385378074021805421575 24063578067111032708132363)
            ·
              refine ⟨36095367100666549062198545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24063578067111032708132363 36095367100666549062198545)
              ·
                refine ⟨27071525325499911796648909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36095367100666549062198545 27071525325499911796648909)
                ·
                  refine ⟨10151821997062466923743341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27071525325499911796648909 10151821997062466923743341)
                  ·
                    refine ⟨3806933248898425096403753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10151821997062466923743341 3806933248898425096403753)
                    ·
                      refine ⟨2855199936673818822302815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806933248898425096403753 2855199936673818822302815)
                      ·
                        rfl

theorem cell23_5560482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5560482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560482 prefixEnd_5560482 := by exact prefixLift 5560482
  have htrace : WordTrace (prefixWord ++ tailWord_5560482) baseStart_5560482 baseEnd_5560482 := by
    simpa [prefixWord, tailWord_5560482, baseEnd_5560482] using wordTrace_append hprefix tailTrace_5560482
  have hstable : (prefixWord ++ tailWord_5560482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560482).length < 2 ^ (prefixWord ++ tailWord_5560482).sum := by decide
  have hdescent : baseEnd_5560482 < baseStart_5560482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560495 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 6, 2, 2]
def baseStart_5560495 : Nat := 118140960795 + 5560495 * 2 ^ 59
def prefixEnd_5560495 : Nat := 4983230072969 + 3 ^ 40 * 5560495 * 2
def baseEnd_5560495 : Nat := 2855206611922327271440255

theorem tailTrace_5560495 : CollatzResearch.WordTrace tailWord_5560495 prefixEnd_5560495 2855206611922327271440255 := by
  unfold tailWord_5560495
  simp only [CollatzResearch.WordTrace]
  refine ⟨202807913990283746785058939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135205275993522497856705959 202807913990283746785058939)
  ·
    refine ⟨304211870985425620177588409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202807913990283746785058939 304211870985425620177588409)
    ·
      refine ⟨228158903239069215133191307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304211870985425620177588409 228158903239069215133191307)
      ·
        refine ⟨342238354858603822699786961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228158903239069215133191307 342238354858603822699786961)
        ·
          refine ⟨256678766143952867024840221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342238354858603822699786961 256678766143952867024840221)
          ·
            refine ⟨96254537303982325134315083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256678766143952867024840221 96254537303982325134315083)
            ·
              refine ⟨144381805955973487701472625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96254537303982325134315083 144381805955973487701472625)
              ·
                refine ⟨108286354466980115776104469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144381805955973487701472625 108286354466980115776104469)
                ·
                  refine ⟨5075922865639692927004897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108286354466980115776104469 5075922865639692927004897)
                  ·
                    refine ⟨3806942149229769695253673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5075922865639692927004897 3806942149229769695253673)
                    ·
                      refine ⟨2855206611922327271440255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806942149229769695253673 2855206611922327271440255)
                      ·
                        rfl

theorem cell23_5560495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2, 2].length) (baseStart_5560495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560495 prefixEnd_5560495 := by exact prefixLift 5560495
  have htrace : WordTrace (prefixWord ++ tailWord_5560495) baseStart_5560495 baseEnd_5560495 := by
    simpa [prefixWord, tailWord_5560495, baseEnd_5560495] using wordTrace_append hprefix tailTrace_5560495
  have hstable : (prefixWord ++ tailWord_5560495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560495).length < 2 ^ (prefixWord ++ tailWord_5560495).sum := by decide
  have hdescent : baseEnd_5560495 < baseStart_5560495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560498 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_5560498 : Nat := 118140960795 + 5560498 * 2 ^ 59
def prefixEnd_5560498 : Nat := 4983230072969 + 3 ^ 40 * 5560498 * 2
def baseEnd_5560498 : Nat := 2855208152364290759702741

theorem tailTrace_5560498 : CollatzResearch.WordTrace tailWord_5560498 prefixEnd_5560498 2855208152364290759702741 := by
  unfold tailWord_5560498
  simp only [CollatzResearch.WordTrace]
  refine ⟨50702005852318219574354537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135205348939515252198278765 50702005852318219574354537)
  ·
    refine ⟨38026504389238664680765903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50702005852318219574354537 38026504389238664680765903)
    ·
      refine ⟨57039756583857997021148855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38026504389238664680765903 57039756583857997021148855)
      ·
        refine ⟨85559634875786995531723283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57039756583857997021148855 85559634875786995531723283)
        ·
          refine ⟨128339452313680493297584925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85559634875786995531723283 128339452313680493297584925)
          ·
            refine ⟨48127294617630184986594347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128339452313680493297584925 48127294617630184986594347)
            ·
              refine ⟨72190941926445277479891521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48127294617630184986594347 72190941926445277479891521)
              ·
                refine ⟨54143206444833958109918641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72190941926445277479891521 54143206444833958109918641)
                ·
                  refine ⟨40607404833625468582438981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54143206444833958109918641 40607404833625468582438981)
                  ·
                    refine ⟨7613888406304775359207309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40607404833625468582438981 7613888406304775359207309)
                    ·
                      refine ⟨2855208152364290759702741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7613888406304775359207309 2855208152364290759702741)
                      ·
                        rfl

theorem cell23_5560498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_5560498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560498 prefixEnd_5560498 := by exact prefixLift 5560498
  have htrace : WordTrace (prefixWord ++ tailWord_5560498) baseStart_5560498 baseEnd_5560498 := by
    simpa [prefixWord, tailWord_5560498, baseEnd_5560498] using wordTrace_append hprefix tailTrace_5560498
  have hstable : (prefixWord ++ tailWord_5560498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560498).length < 2 ^ (prefixWord ++ tailWord_5560498).sum := by decide
  have hdescent : baseEnd_5560498 < baseStart_5560498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_5560511 : Nat := 118140960795 + 5560511 * 2 ^ 59
def prefixEnd_5560511 : Nat := 4983230072969 + 3 ^ 40 * 5560511 * 2
def baseEnd_5560511 : Nat := 2855214827612799208840181

theorem tailTrace_5560511 : CollatzResearch.WordTrace tailWord_5560511 prefixEnd_5560511 2855214827612799208840181 := by
  unfold tailWord_5560511
  simp only [CollatzResearch.WordTrace]
  refine ⟨202808497558225781517641387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135205665038817187678427591 202808497558225781517641387)
  ·
    refine ⟨304212746337338672276462081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202808497558225781517641387 304212746337338672276462081)
    ·
      refine ⟨228159559753004004207346561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304212746337338672276462081 228159559753004004207346561)
      ·
        refine ⟨171119669814753003155509921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228159559753004004207346561 171119669814753003155509921)
        ·
          refine ⟨128339752361064752366632441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171119669814753003155509921 128339752361064752366632441)
          ·
            refine ⟨96254814270798564274974331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128339752361064752366632441 96254814270798564274974331)
            ·
              refine ⟨144382221406197846412461497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96254814270798564274974331 144382221406197846412461497)
              ·
                refine ⟨108286666054648384809346123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144382221406197846412461497 108286666054648384809346123)
                ·
                  refine ⟨162429999081972577214019185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108286666054648384809346123 162429999081972577214019185)
                  ·
                    refine ⟨121822499311479432910514389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162429999081972577214019185 121822499311479432910514389)
                    ·
                      refine ⟨2855214827612799208840181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121822499311479432910514389 2855214827612799208840181)
                      ·
                        rfl

theorem cell23_5560511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_5560511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560511 prefixEnd_5560511 := by exact prefixLift 5560511
  have htrace : WordTrace (prefixWord ++ tailWord_5560511) baseStart_5560511 baseEnd_5560511 := by
    simpa [prefixWord, tailWord_5560511, baseEnd_5560511] using wordTrace_append hprefix tailTrace_5560511
  have hstable : (prefixWord ++ tailWord_5560511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560511).length < 2 ^ (prefixWord ++ tailWord_5560511).sum := by decide
  have hdescent : baseEnd_5560511 < baseStart_5560511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560516 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_5560516 : Nat := 118140960795 + 5560516 * 2 ^ 59
def prefixEnd_5560516 : Nat := 4983230072969 + 3 ^ 40 * 5560516 * 2
def baseEnd_5560516 : Nat := 2855217395016071689277659

theorem tailTrace_5560516 : CollatzResearch.WordTrace tailWord_5560516 prefixEnd_5560516 2855217395016071689277659 := by
  unfold tailWord_5560516
  simp only [CollatzResearch.WordTrace]
  refine ⟨101404339961603833685786701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135205786615471778247715601 101404339961603833685786701)
  ·
    refine ⟨38026627485601437632170013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101404339961603833685786701 38026627485601437632170013)
    ·
      refine ⟨14259985307100539112063755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38026627485601437632170013 14259985307100539112063755)
      ·
        refine ⟨21389977960650808668095633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14259985307100539112063755 21389977960650808668095633)
        ·
          refine ⟨16042483470488106501071725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21389977960650808668095633 16042483470488106501071725)
          ·
            refine ⟨6015931301433039937901897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16042483470488106501071725 6015931301433039937901897)
            ·
              refine ⟨4511948476074779953426423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015931301433039937901897 4511948476074779953426423)
              ·
                refine ⟨6767922714112169930139635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511948476074779953426423 6767922714112169930139635)
                ·
                  refine ⟨10151884071168254895209453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767922714112169930139635 10151884071168254895209453)
                  ·
                    refine ⟨3806956526688095585703545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10151884071168254895209453 3806956526688095585703545)
                    ·
                      refine ⟨2855217395016071689277659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3806956526688095585703545 2855217395016071689277659)
                      ·
                        rfl

theorem cell23_5560516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_5560516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560516 prefixEnd_5560516 := by exact prefixLift 5560516
  have htrace : WordTrace (prefixWord ++ tailWord_5560516) baseStart_5560516 baseEnd_5560516 := by
    simpa [prefixWord, tailWord_5560516, baseEnd_5560516] using wordTrace_append hprefix tailTrace_5560516
  have hstable : (prefixWord ++ tailWord_5560516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560516).length < 2 ^ (prefixWord ++ tailWord_5560516).sum := by decide
  have hdescent : baseEnd_5560516 < baseStart_5560516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 7]
def baseStart_5560531 : Nat := 118140960795 + 5560531 * 2 ^ 59
def prefixEnd_5560531 : Nat := 4983230072969 + 3 ^ 40 * 5560531 * 2
def baseEnd_5560531 : Nat := 951741699075296376863363

theorem tailTrace_5560531 : CollatzResearch.WordTrace tailWord_5560531 prefixEnd_5560531 951741699075296376863363 := by
  unfold tailWord_5560531
  simp only [CollatzResearch.WordTrace]
  refine ⟨202809227018153324933369447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135206151345435549955579631 202809227018153324933369447)
  ·
    refine ⟨304213840527229987400054171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202809227018153324933369447 304213840527229987400054171)
    ·
      refine ⟨456320760790844981100081257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304213840527229987400054171 456320760790844981100081257)
      ·
        refine ⟨342240570593133735825060943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456320760790844981100081257 342240570593133735825060943)
        ·
          refine ⟨513360855889700603737591415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342240570593133735825060943 513360855889700603737591415)
          ·
            refine ⟨770041283834550905606387123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513360855889700603737591415 770041283834550905606387123)
            ·
              refine ⟨1155061925751826358409580685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770041283834550905606387123 1155061925751826358409580685)
              ·
                refine ⟨433148222156934884403592757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1155061925751826358409580685 433148222156934884403592757)
                ·
                  refine ⟨40607645827212645412836821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433148222156934884403592757 40607645827212645412836821)
                  ·
                    refine ⟨951741699075296376863363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40607645827212645412836821 951741699075296376863363)
                    ·
                      rfl

theorem cell23_5560531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_5560531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560531 prefixEnd_5560531 := by exact prefixLift 5560531
  have htrace : WordTrace (prefixWord ++ tailWord_5560531) baseStart_5560531 baseEnd_5560531 := by
    simpa [prefixWord, tailWord_5560531, baseEnd_5560531] using wordTrace_append hprefix tailTrace_5560531
  have hstable : (prefixWord ++ tailWord_5560531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560531).length < 2 ^ (prefixWord ++ tailWord_5560531).sum := by decide
  have hdescent : baseEnd_5560531 < baseStart_5560531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560558 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5560558 : Nat := 118140960795 + 5560558 * 2 ^ 59
def prefixEnd_5560558 : Nat := 4983230072969 + 3 ^ 40 * 5560558 * 2
def baseEnd_5560558 : Nat := 2855238961203560524952465

theorem tailTrace_5560558 : CollatzResearch.WordTrace tailWord_5560558 prefixEnd_5560558 2855238961203560524952465 := by
  unfold tailWord_5560558
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351276473631938568075291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135206807859370339029734885 25351276473631938568075291)
  ·
    refine ⟨38026914710447907852112937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25351276473631938568075291 38026914710447907852112937)
    ·
      refine ⟨28520186032835930889084703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38026914710447907852112937 28520186032835930889084703)
      ·
        refine ⟨42780279049253896333627055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28520186032835930889084703 42780279049253896333627055)
        ·
          refine ⟨64170418573880844500440583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42780279049253896333627055 64170418573880844500440583)
          ·
            refine ⟨96255627860821266750660875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64170418573880844500440583 96255627860821266750660875)
            ·
              refine ⟨144383441791231900125991313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96255627860821266750660875 144383441791231900125991313)
              ·
                refine ⟨108287581343423925094493485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144383441791231900125991313 108287581343423925094493485)
                ·
                  refine ⟨40607843003783971910435057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108287581343423925094493485 40607843003783971910435057)
                  ·
                    refine ⟨30455882252837978932826293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40607843003783971910435057 30455882252837978932826293)
                    ·
                      refine ⟨2855238961203560524952465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30455882252837978932826293 2855238961203560524952465)
                      ·
                        rfl

theorem cell23_5560558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5560558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560558 prefixEnd_5560558 := by exact prefixLift 5560558
  have htrace : WordTrace (prefixWord ++ tailWord_5560558) baseStart_5560558 baseEnd_5560558 := by
    simpa [prefixWord, tailWord_5560558, baseEnd_5560558] using wordTrace_append hprefix tailTrace_5560558
  have hstable : (prefixWord ++ tailWord_5560558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560558).length < 2 ^ (prefixWord ++ tailWord_5560558).sum := by decide
  have hdescent : baseEnd_5560558 < baseStart_5560558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560568 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_5560568 : Nat := 118140960795 + 5560568 * 2 ^ 59
def prefixEnd_5560568 : Nat := 4983230072969 + 3 ^ 40 * 5560568 * 2
def baseEnd_5560568 : Nat := 2855244096010105485827419

theorem tailTrace_5560568 : CollatzResearch.WordTrace tailWord_5560568 prefixEnd_5560568 2855244096010105485827419 := by
  unfold tailWord_5560568
  simp only [CollatzResearch.WordTrace]
  refine ⟨101405288259509640126233179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135207051012679520168310905 101405288259509640126233179)
  ·
    refine ⟨152107932389264460189349769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101405288259509640126233179 152107932389264460189349769)
    ·
      refine ⟨114080949291948345142012327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152107932389264460189349769 114080949291948345142012327)
      ·
        refine ⟨171121423937922517713018491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114080949291948345142012327 171121423937922517713018491)
        ·
          refine ⟨256682135906883776569527737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171121423937922517713018491 256682135906883776569527737)
          ·
            refine ⟨192511601930162832427145803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256682135906883776569527737 192511601930162832427145803)
            ·
              refine ⟨288767402895244248640718705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192511601930162832427145803 288767402895244248640718705)
              ·
                refine ⟨216575552171433186480539029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288767402895244248640718705 216575552171433186480539029)
                ·
                  refine ⟨10151979008035930616275267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216575552171433186480539029 10151979008035930616275267)
                  ·
                    refine ⟨15227968512053895924412901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10151979008035930616275267 15227968512053895924412901)
                    ·
                      refine ⟨2855244096010105485827419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15227968512053895924412901 2855244096010105485827419)
                      ·
                        rfl

theorem cell23_5560568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_5560568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560568 prefixEnd_5560568 := by exact prefixLift 5560568
  have htrace : WordTrace (prefixWord ++ tailWord_5560568) baseStart_5560568 baseEnd_5560568 := by
    simpa [prefixWord, tailWord_5560568, baseEnd_5560568] using wordTrace_append hprefix tailTrace_5560568
  have hstable : (prefixWord ++ tailWord_5560568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560568).length < 2 ^ (prefixWord ++ tailWord_5560568).sum := by decide
  have hdescent : baseEnd_5560568 < baseStart_5560568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560585 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_5560585 : Nat := 118140960795 + 5560585 * 2 ^ 59
def prefixEnd_5560585 : Nat := 4983230072969 + 3 ^ 40 * 5560585 * 2
def baseEnd_5560585 : Nat := 2855252825181231919314841

theorem tailTrace_5560585 : CollatzResearch.WordTrace tailWord_5560585 prefixEnd_5560585 2855252825181231919314841 := by
  unfold tailWord_5560585
  simp only [CollatzResearch.WordTrace]
  refine ⟨202811196559957692155835209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135207464373305128103890139 202811196559957692155835209)
  ·
    refine ⟨152108397419968269116876407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202811196559957692155835209 152108397419968269116876407)
    ·
      refine ⟨228162596129952403675314611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152108397419968269116876407 228162596129952403675314611)
      ·
        refine ⟨342243894194928605512971917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228162596129952403675314611 342243894194928605512971917)
        ·
          refine ⟨128341460323098227067364469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342243894194928605512971917 128341460323098227067364469)
          ·
            refine ⟨12032011905290458787565419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128341460323098227067364469 12032011905290458787565419)
            ·
              refine ⟨18048017857935688181348129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032011905290458787565419 18048017857935688181348129)
              ·
                refine ⟨13536013393451766136011097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18048017857935688181348129 13536013393451766136011097)
                ·
                  refine ⟨10152010045088824602008323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13536013393451766136011097 10152010045088824602008323)
                  ·
                    refine ⟨15228015067633236903012485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10152010045088824602008323 15228015067633236903012485)
                    ·
                      refine ⟨2855252825181231919314841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15228015067633236903012485 2855252825181231919314841)
                      ·
                        rfl

theorem cell23_5560585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_5560585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560585 prefixEnd_5560585 := by exact prefixLift 5560585
  have htrace : WordTrace (prefixWord ++ tailWord_5560585) baseStart_5560585 baseEnd_5560585 := by
    simpa [prefixWord, tailWord_5560585, baseEnd_5560585] using wordTrace_append hprefix tailTrace_5560585
  have hstable : (prefixWord ++ tailWord_5560585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560585).length < 2 ^ (prefixWord ++ tailWord_5560585).sum := by decide
  have hdescent : baseEnd_5560585 < baseStart_5560585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560645 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_5560645 : Nat := 118140960795 + 5560645 * 2 ^ 59
def prefixEnd_5560645 : Nat := 4983230072969 + 3 ^ 40 * 5560645 * 2
def baseEnd_5560645 : Nat := 2855283634020501684564565

theorem tailTrace_5560645 : CollatzResearch.WordTrace tailWord_5560645 prefixEnd_5560645 2855283634020501684564565 := by
  unfold tailWord_5560645
  simp only [CollatzResearch.WordTrace]
  refine ⟨202813384939740322403019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135208923293160214935346259 202813384939740322403019389)
  ·
    refine ⟨76055019352402620901132271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202813384939740322403019389 76055019352402620901132271)
    ·
      refine ⟨114082529028603931351698407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76055019352402620901132271 114082529028603931351698407)
      ·
        refine ⟨171123793542905897027547611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114082529028603931351698407 171123793542905897027547611)
        ·
          refine ⟨256685690314358845541321417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171123793542905897027547611 256685690314358845541321417)
          ·
            refine ⟨192514267735769134155991063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256685690314358845541321417 192514267735769134155991063)
            ·
              refine ⟨288771401603653701233986595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192514267735769134155991063 288771401603653701233986595)
              ·
                refine ⟨433157102405480551850979893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288771401603653701233986595 433157102405480551850979893)
                ·
                  refine ⟨40608478350513801736029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433157102405480551850979893 40608478350513801736029365)
                  ·
                    refine ⟨3807044845360668912752753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40608478350513801736029365 3807044845360668912752753)
                    ·
                      refine ⟨2855283634020501684564565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807044845360668912752753 2855283634020501684564565)
                      ·
                        rfl

theorem cell23_5560645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_5560645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560645 prefixEnd_5560645 := by exact prefixLift 5560645
  have htrace : WordTrace (prefixWord ++ tailWord_5560645) baseStart_5560645 baseEnd_5560645 := by
    simpa [prefixWord, tailWord_5560645, baseEnd_5560645] using wordTrace_append hprefix tailTrace_5560645
  have hstable : (prefixWord ++ tailWord_5560645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560645).length < 2 ^ (prefixWord ++ tailWord_5560645).sum := by decide
  have hdescent : baseEnd_5560645 < baseStart_5560645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560652 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5560652 : Nat := 118140960795 + 5560652 * 2 ^ 59
def prefixEnd_5560652 : Nat := 4983230072969 + 3 ^ 40 * 5560652 * 2
def baseEnd_5560652 : Nat := 2855287228385083157177033

theorem tailTrace_5560652 : CollatzResearch.WordTrace tailWord_5560652 prefixEnd_5560652 2855287228385083157177033 := by
  unfold tailWord_5560652
  simp only [CollatzResearch.WordTrace]
  refine ⟨101406820125357481299262105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135209093500476641732349473 101406820125357481299262105)
  ·
    refine ⟨76055115094018110974446579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101406820125357481299262105 76055115094018110974446579)
    ·
      refine ⟨114082672641027166461669869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76055115094018110974446579 114082672641027166461669869)
      ·
        refine ⟨42781002240385187423126201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114082672641027166461669869 42781002240385187423126201)
        ·
          refine ⟨32085751680288890567344651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42781002240385187423126201 32085751680288890567344651)
          ·
            refine ⟨48128627520433335851016977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32085751680288890567344651 48128627520433335851016977)
            ·
              refine ⟨36096470640325001888262733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48128627520433335851016977 36096470640325001888262733)
              ·
                refine ⟨13536176490121875708098525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36096470640325001888262733 13536176490121875708098525)
                ·
                  refine ⟨5076066183795703390536947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13536176490121875708098525 5076066183795703390536947)
                  ·
                    refine ⟨7614099275693555085805421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076066183795703390536947 7614099275693555085805421)
                    ·
                      refine ⟨2855287228385083157177033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614099275693555085805421 2855287228385083157177033)
                      ·
                        rfl

theorem cell23_5560652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5560652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560652 prefixEnd_5560652 := by exact prefixLift 5560652
  have htrace : WordTrace (prefixWord ++ tailWord_5560652) baseStart_5560652 baseEnd_5560652 := by
    simpa [prefixWord, tailWord_5560652, baseEnd_5560652] using wordTrace_append hprefix tailTrace_5560652
  have hstable : (prefixWord ++ tailWord_5560652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560652).length < 2 ^ (prefixWord ++ tailWord_5560652).sum := by decide
  have hdescent : baseEnd_5560652 < baseStart_5560652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560670 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5560670 : Nat := 118140960795 + 5560670 * 2 ^ 59
def prefixEnd_5560670 : Nat := 4983230072969 + 3 ^ 40 * 5560670 * 2
def baseEnd_5560670 : Nat := 2855296471036864086751951

theorem tailTrace_5560670 : CollatzResearch.WordTrace tailWord_5560670 prefixEnd_5560670 2855296471036864086751951 := by
  unfold tailWord_5560670
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351787095581218959084933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135209531176433167781786309 25351787095581218959084933)
  ·
    refine ⟨4753460080421478554828425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25351787095581218959084933 4753460080421478554828425)
    ·
      refine ⟨3565095060316108916121319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4753460080421478554828425 3565095060316108916121319)
      ·
        refine ⟨5347642590474163374181979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565095060316108916121319 5347642590474163374181979)
        ·
          refine ⟨8021463885711245061272969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347642590474163374181979 8021463885711245061272969)
          ·
            refine ⟨6016097914283433795954727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8021463885711245061272969 6016097914283433795954727)
            ·
              refine ⟨9024146871425150693932091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016097914283433795954727 9024146871425150693932091)
              ·
                refine ⟨13536220307137726040898137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024146871425150693932091 13536220307137726040898137)
                ·
                  refine ⟨10152165230353294530673603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13536220307137726040898137 10152165230353294530673603)
                  ·
                    refine ⟨15228247845529941796010405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10152165230353294530673603 15228247845529941796010405)
                    ·
                      refine ⟨2855296471036864086751951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15228247845529941796010405 2855296471036864086751951)
                      ·
                        rfl

theorem cell23_5560670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5560670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560670 prefixEnd_5560670 := by exact prefixLift 5560670
  have htrace : WordTrace (prefixWord ++ tailWord_5560670) baseStart_5560670 baseEnd_5560670 := by
    simpa [prefixWord, tailWord_5560670, baseEnd_5560670] using wordTrace_append hprefix tailTrace_5560670
  have hstable : (prefixWord ++ tailWord_5560670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560670).length < 2 ^ (prefixWord ++ tailWord_5560670).sum := by decide
  have hdescent : baseEnd_5560670 < baseStart_5560670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560675 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5560675 : Nat := 118140960795 + 5560675 * 2 ^ 59
def prefixEnd_5560675 : Nat := 4983230072969 + 3 ^ 40 * 5560675 * 2
def baseEnd_5560675 : Nat := 2855299038440136567189427

theorem tailTrace_5560675 : CollatzResearch.WordTrace tailWord_5560675 prefixEnd_5560675 2855299038440136567189427 := by
  unfold tailWord_5560675
  simp only [CollatzResearch.WordTrace]
  refine ⟨202814479129631637526611479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135209652753087758351074319 202814479129631637526611479)
  ·
    refine ⟨304221718694447456289917219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202814479129631637526611479 304221718694447456289917219)
    ·
      refine ⟨456332578041671184434875829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304221718694447456289917219 456332578041671184434875829)
      ·
        refine ⟨42781179191406673540769609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 456332578041671184434875829 42781179191406673540769609)
        ·
          refine ⟨32085884393555005155577207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42781179191406673540769609 32085884393555005155577207)
          ·
            refine ⟨48128826590332507733365811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32085884393555005155577207 48128826590332507733365811)
            ·
              refine ⟨72193239885498761600048717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48128826590332507733365811 72193239885498761600048717)
              ·
                refine ⟨27072464957062035600018269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72193239885498761600048717 27072464957062035600018269)
                ·
                  refine ⟨10152174358898263350006851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27072464957062035600018269 10152174358898263350006851)
                  ·
                    refine ⟨15228261538347395025010277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10152174358898263350006851 15228261538347395025010277)
                    ·
                      refine ⟨2855299038440136567189427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15228261538347395025010277 2855299038440136567189427)
                      ·
                        rfl

theorem cell23_5560675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5560675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560675 prefixEnd_5560675 := by exact prefixLift 5560675
  have htrace : WordTrace (prefixWord ++ tailWord_5560675) baseStart_5560675 baseEnd_5560675 := by
    simpa [prefixWord, tailWord_5560675, baseEnd_5560675] using wordTrace_append hprefix tailTrace_5560675
  have hstable : (prefixWord ++ tailWord_5560675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560675).length < 2 ^ (prefixWord ++ tailWord_5560675).sum := by decide
  have hdescent : baseEnd_5560675 < baseStart_5560675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560679 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_5560679 : Nat := 118140960795 + 5560679 * 2 ^ 59
def prefixEnd_5560679 : Nat := 4983230072969 + 3 ^ 40 * 5560679 * 2
def baseEnd_5560679 : Nat := 2855301092362754551539409

theorem tailTrace_5560679 : CollatzResearch.WordTrace tailWord_5560679 prefixEnd_5560679 2855301092362754551539409 := by
  unfold tailWord_5560679
  simp only [CollatzResearch.WordTrace]
  refine ⟨202814625021617146209757091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135209750014411430806504727 202814625021617146209757091)
  ·
    refine ⟨304221937532425719314635637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202814625021617146209757091 304221937532425719314635637)
    ·
      refine ⟨28520806643664911185747091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304221937532425719314635637 28520806643664911185747091)
      ·
        refine ⟨42781209965497366778620637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28520806643664911185747091 42781209965497366778620637)
        ·
          refine ⟨16042953737061512541982739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42781209965497366778620637 16042953737061512541982739)
          ·
            refine ⟨24064430605592268812974109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16042953737061512541982739 24064430605592268812974109)
            ·
              refine ⟨9024161477097100804865291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24064430605592268812974109 9024161477097100804865291)
              ·
                refine ⟨13536242215645651207297937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024161477097100804865291 13536242215645651207297937)
                ·
                  refine ⟨10152181661734238405473453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13536242215645651207297937 10152181661734238405473453)
                  ·
                    refine ⟨3807068123150339402052545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10152181661734238405473453 3807068123150339402052545)
                    ·
                      refine ⟨2855301092362754551539409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807068123150339402052545 2855301092362754551539409)
                      ·
                        rfl

theorem cell23_5560679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_5560679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560679 prefixEnd_5560679 := by exact prefixLift 5560679
  have htrace : WordTrace (prefixWord ++ tailWord_5560679) baseStart_5560679 baseEnd_5560679 := by
    simpa [prefixWord, tailWord_5560679, baseEnd_5560679] using wordTrace_append hprefix tailTrace_5560679
  have hstable : (prefixWord ++ tailWord_5560679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560679).length < 2 ^ (prefixWord ++ tailWord_5560679).sum := by decide
  have hdescent : baseEnd_5560679 < baseStart_5560679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560685 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_5560685 : Nat := 118140960795 + 5560685 * 2 ^ 59
def prefixEnd_5560685 : Nat := 4983230072969 + 3 ^ 40 * 5560685 * 2
def baseEnd_5560685 : Nat := 951768057748893842688127

theorem tailTrace_5560685 : CollatzResearch.WordTrace tailWord_5560685 prefixEnd_5560685 951768057748893842688127 := by
  unfold tailWord_5560685
  simp only [CollatzResearch.WordTrace]
  refine ⟨202814843859595409234475509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135209895906396939489650339 202814843859595409234475509)
  ·
    refine ⟨19013891611837069615732079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202814843859595409234475509 19013891611837069615732079)
    ·
      refine ⟨28520837417755604423598119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19013891611837069615732079 28520837417755604423598119)
      ·
        refine ⟨42781256126633406635397179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28520837417755604423598119 42781256126633406635397179)
        ·
          refine ⟨64171884189950109953095769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42781256126633406635397179 64171884189950109953095769)
          ·
            refine ⟨48128913142462582464821827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64171884189950109953095769 48128913142462582464821827)
            ·
              refine ⟨72193369713693873697232741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48128913142462582464821827 72193369713693873697232741)
              ·
                refine ⟨13536256821317601318231139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72193369713693873697232741 13536256821317601318231139)
                ·
                  refine ⟨20304385231976401977346709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13536256821317601318231139 20304385231976401977346709)
                  ·
                    refine ⟨951768057748893842688127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20304385231976401977346709 951768057748893842688127)
                    ·
                      rfl

theorem cell23_5560685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_5560685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560685 prefixEnd_5560685 := by exact prefixLift 5560685
  have htrace : WordTrace (prefixWord ++ tailWord_5560685) baseStart_5560685 baseEnd_5560685 := by
    simpa [prefixWord, tailWord_5560685, baseEnd_5560685] using wordTrace_append hprefix tailTrace_5560685
  have hstable : (prefixWord ++ tailWord_5560685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560685).length < 2 ^ (prefixWord ++ tailWord_5560685).sum := by decide
  have hdescent : baseEnd_5560685 < baseStart_5560685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560695 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_5560695 : Nat := 118140960795 + 5560695 * 2 ^ 59
def prefixEnd_5560695 : Nat := 4983230072969 + 3 ^ 40 * 5560695 * 2
def baseEnd_5560695 : Nat := 2855309308053226488939335

theorem tailTrace_5560695 : CollatzResearch.WordTrace tailWord_5560695 prefixEnd_5560695 2855309308053226488939335 := by
  unfold tailWord_5560695
  simp only [CollatzResearch.WordTrace]
  refine ⟨202815208589559180942339539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135210139059706120628226359 202815208589559180942339539)
  ·
    refine ⟨304222812884338771413509309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202815208589559180942339539 304222812884338771413509309)
    ·
      refine ⟨114083554831627039280065991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304222812884338771413509309 114083554831627039280065991)
      ·
        refine ⟨171125332247440558920098987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114083554831627039280065991 171125332247440558920098987)
        ·
          refine ⟨256687998371160838380148481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171125332247440558920098987 256687998371160838380148481)
          ·
            refine ⟨192515998778370628785111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256687998371160838380148481 192515998778370628785111361)
            ·
              refine ⟨144386999083777971588833521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192515998778370628785111361 144386999083777971588833521)
              ·
                refine ⟨108290249312833478691625141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144386999083777971588833521 108290249312833478691625141)
                ·
                  refine ⟨10152210873078138627339857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108290249312833478691625141 10152210873078138627339857)
                  ·
                    refine ⟨7614158154808603970504893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10152210873078138627339857 7614158154808603970504893)
                    ·
                      refine ⟨2855309308053226488939335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614158154808603970504893 2855309308053226488939335)
                      ·
                        rfl

theorem cell23_5560695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_5560695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560695 prefixEnd_5560695 := by exact prefixLift 5560695
  have htrace : WordTrace (prefixWord ++ tailWord_5560695) baseStart_5560695 baseEnd_5560695 := by
    simpa [prefixWord, tailWord_5560695, baseEnd_5560695] using wordTrace_append hprefix tailTrace_5560695
  have hstable : (prefixWord ++ tailWord_5560695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560695).length < 2 ^ (prefixWord ++ tailWord_5560695).sum := by decide
  have hdescent : baseEnd_5560695 < baseStart_5560695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560743 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5560743 : Nat := 118140960795 + 5560743 * 2 ^ 59
def prefixEnd_5560743 : Nat := 4983230072969 + 3 ^ 40 * 5560743 * 2
def baseEnd_5560743 : Nat := 2855333955124642301139115

theorem tailTrace_5560743 : CollatzResearch.WordTrace tailWord_5560743 prefixEnd_5560743 2855333955124642301139115 := by
  unfold tailWord_5560743
  simp only [CollatzResearch.WordTrace]
  refine ⟨202816959293385285140086883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135211306195590190093391255 202816959293385285140086883)
  ·
    refine ⟨304225438940077927710130325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202816959293385285140086883 304225438940077927710130325)
    ·
      refine ⟨14260567450316152861412359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304225438940077927710130325 14260567450316152861412359)
      ·
        refine ⟨21390851175474229292118539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14260567450316152861412359 21390851175474229292118539)
        ·
          refine ⟨32086276763211343938177809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21390851175474229292118539 32086276763211343938177809)
          ·
            refine ⟨24064707572408507953633357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32086276763211343938177809 24064707572408507953633357)
            ·
              refine ⟨9024265339653190482612509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24064707572408507953633357 9024265339653190482612509)
              ·
                refine ⟨3384099502369946430979691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9024265339653190482612509 3384099502369946430979691)
                ·
                  refine ⟨5076149253554919646469537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384099502369946430979691 5076149253554919646469537)
                  ·
                    refine ⟨3807111940166189734852153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076149253554919646469537 3807111940166189734852153)
                    ·
                      refine ⟨2855333955124642301139115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807111940166189734852153 2855333955124642301139115)
                      ·
                        rfl

theorem cell23_5560743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5560743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560743 prefixEnd_5560743 := by exact prefixLift 5560743
  have htrace : WordTrace (prefixWord ++ tailWord_5560743) baseStart_5560743 baseEnd_5560743 := by
    simpa [prefixWord, tailWord_5560743, baseEnd_5560743] using wordTrace_append hprefix tailTrace_5560743
  have hstable : (prefixWord ++ tailWord_5560743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560743).length < 2 ^ (prefixWord ++ tailWord_5560743).sum := by decide
  have hdescent : baseEnd_5560743 < baseStart_5560743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560749 : List Nat := [1, 5, 2, 2, 3, 1, 9]
def baseStart_5560749 : Nat := 118140960795 + 5560749 * 2 ^ 59
def prefixEnd_5560749 : Nat := 4983230072969 + 3 ^ 40 * 5560749 * 2
def baseEnd_5560749 : Nat := 35251074518624312069927

theorem tailTrace_5560749 : CollatzResearch.WordTrace tailWord_5560749 prefixEnd_5560749 35251074518624312069927 := by
  unfold tailWord_5560749
  simp only [CollatzResearch.WordTrace]
  refine ⟨202817178131363548164805301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135211452087575698776536867 202817178131363548164805301)
  ·
    refine ⟨19014110449815332640450497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202817178131363548164805301 19014110449815332640450497)
    ·
      refine ⟨14260582837361499480337873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19014110449815332640450497 14260582837361499480337873)
      ·
        refine ⟨10695437128021124610253405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14260582837361499480337873 10695437128021124610253405)
        ·
          refine ⟨4010788923007921728845027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10695437128021124610253405 4010788923007921728845027)
          ·
            refine ⟨6016183384511882593267541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010788923007921728845027 6016183384511882593267541)
            ·
              refine ⟨35251074518624312069927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6016183384511882593267541 35251074518624312069927)
              ·
                rfl

theorem cell23_5560749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 9].length) (baseStart_5560749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560749 prefixEnd_5560749 := by exact prefixLift 5560749
  have htrace : WordTrace (prefixWord ++ tailWord_5560749) baseStart_5560749 baseEnd_5560749 := by
    simpa [prefixWord, tailWord_5560749, baseEnd_5560749] using wordTrace_append hprefix tailTrace_5560749
  have hstable : (prefixWord ++ tailWord_5560749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560749).length < 2 ^ (prefixWord ++ tailWord_5560749).sum := by decide
  have hdescent : baseEnd_5560749 < baseStart_5560749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560776 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_5560776 : Nat := 118140960795 + 5560776 * 2 ^ 59
def prefixEnd_5560776 : Nat := 4983230072969 + 3 ^ 40 * 5560776 * 2
def baseEnd_5560776 : Nat := 2855350899986240672026463

theorem tailTrace_5560776 : CollatzResearch.WordTrace tailWord_5560776 prefixEnd_5560776 2855350899986240672026463 := by
  unfold tailWord_5560776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101409081451132865888019091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135212108601510487850692121 101409081451132865888019091)
  ·
    refine ⟨152113622176699298832028637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101409081451132865888019091 152113622176699298832028637)
    ·
      refine ⟨57042608316262237062010739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152113622176699298832028637 57042608316262237062010739)
      ·
        refine ⟨85563912474393355593016109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57042608316262237062010739 85563912474393355593016109)
        ·
          refine ⟨32086467177897508347381041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85563912474393355593016109 32086467177897508347381041)
          ·
            refine ⟨24064850383423131260535781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32086467177897508347381041 24064850383423131260535781)
            ·
              refine ⟨4512159446891837111350459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24064850383423131260535781 4512159446891837111350459)
              ·
                refine ⟨6768239170337755667025689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512159446891837111350459 6768239170337755667025689)
                ·
                  refine ⟨5076179377753316750269267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768239170337755667025689 5076179377753316750269267)
                  ·
                    refine ⟨7614269066629975125403901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076179377753316750269267 7614269066629975125403901)
                    ·
                      refine ⟨2855350899986240672026463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614269066629975125403901 2855350899986240672026463)
                      ·
                        rfl

theorem cell23_5560776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_5560776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560776 prefixEnd_5560776 := by exact prefixLift 5560776
  have htrace : WordTrace (prefixWord ++ tailWord_5560776) baseStart_5560776 baseEnd_5560776 := by
    simpa [prefixWord, tailWord_5560776, baseEnd_5560776] using wordTrace_append hprefix tailTrace_5560776
  have hstable : (prefixWord ++ tailWord_5560776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560776).length < 2 ^ (prefixWord ++ tailWord_5560776).sum := by decide
  have hdescent : baseEnd_5560776 < baseStart_5560776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560799 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 4, 2]
def baseStart_5560799 : Nat := 118140960795 + 5560799 * 2 ^ 59
def prefixEnd_5560799 : Nat := 4983230072969 + 3 ^ 40 * 5560799 * 2
def baseEnd_5560799 : Nat := 2855362710041294082038857

theorem tailTrace_5560799 : CollatzResearch.WordTrace tailWord_5560799 prefixEnd_5560799 2855362710041294082038857 := by
  unfold tailWord_5560799
  simp only [CollatzResearch.WordTrace]
  refine ⟨202819001781182406704125451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135212667854121604469416967 202819001781182406704125451)
  ·
    refine ⟨304228502671773610056188177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202819001781182406704125451 304228502671773610056188177)
    ·
      refine ⟨228171377003830207542141133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304228502671773610056188177 228171377003830207542141133)
      ·
        refine ⟨85564266376436327828302925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228171377003830207542141133 85564266376436327828302925)
        ·
          refine ⟨32086599891163622935613597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85564266376436327828302925 32086599891163622935613597)
          ·
            refine ⟨12032474959186358600855099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32086599891163622935613597 12032474959186358600855099)
            ·
              refine ⟨18048712438779537901282649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032474959186358600855099 18048712438779537901282649)
              ·
                refine ⟨13536534329084653425961987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18048712438779537901282649 13536534329084653425961987)
                ·
                  refine ⟨20304801493626980138942981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13536534329084653425961987 20304801493626980138942981)
                  ·
                    refine ⟨3807150280055058776051809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20304801493626980138942981 3807150280055058776051809)
                    ·
                      refine ⟨2855362710041294082038857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807150280055058776051809 2855362710041294082038857)
                      ·
                        rfl

theorem cell23_5560799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_5560799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560799 prefixEnd_5560799 := by exact prefixLift 5560799
  have htrace : WordTrace (prefixWord ++ tailWord_5560799) baseStart_5560799 baseEnd_5560799 := by
    simpa [prefixWord, tailWord_5560799, baseEnd_5560799] using wordTrace_append hprefix tailTrace_5560799
  have hstable : (prefixWord ++ tailWord_5560799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560799).length < 2 ^ (prefixWord ++ tailWord_5560799).sum := by decide
  have hdescent : baseEnd_5560799 < baseStart_5560799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560803 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5560803 : Nat := 118140960795 + 5560803 * 2 ^ 59
def prefixEnd_5560803 : Nat := 4983230072969 + 3 ^ 40 * 5560803 * 2
def baseEnd_5560803 : Nat := 2855364763963912066388839

theorem tailTrace_5560803 : CollatzResearch.WordTrace tailWord_5560803 prefixEnd_5560803 2855364763963912066388839 := by
  unfold tailWord_5560803
  simp only [CollatzResearch.WordTrace]
  refine ⟨202819147673167915387271063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135212765115445276924847375 202819147673167915387271063)
  ·
    refine ⟨304228721509751873080906595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202819147673167915387271063 304228721509751873080906595)
    ·
      refine ⟨456343082264627809621359893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304228721509751873080906595 456343082264627809621359893)
      ·
        refine ⟨21391081981154428576001245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 456343082264627809621359893 21391081981154428576001245)
        ·
          refine ⟨8021655742932910716000467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21391081981154428576001245 8021655742932910716000467)
          ·
            refine ⟨12032483614399366074000701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021655742932910716000467 12032483614399366074000701)
            ·
              refine ⟨4512181355399762277750263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12032483614399366074000701 4512181355399762277750263)
              ·
                refine ⟨6768272033099643416625395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512181355399762277750263 6768272033099643416625395)
                ·
                  refine ⟨10152408049649465124938093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768272033099643416625395 10152408049649465124938093)
                  ·
                    refine ⟨3807153018618549421851785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10152408049649465124938093 3807153018618549421851785)
                    ·
                      refine ⟨2855364763963912066388839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807153018618549421851785 2855364763963912066388839)
                      ·
                        rfl

theorem cell23_5560803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5560803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560803 prefixEnd_5560803 := by exact prefixLift 5560803
  have htrace : WordTrace (prefixWord ++ tailWord_5560803) baseStart_5560803 baseEnd_5560803 := by
    simpa [prefixWord, tailWord_5560803, baseEnd_5560803] using wordTrace_append hprefix tailTrace_5560803
  have hstable : (prefixWord ++ tailWord_5560803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560803).length < 2 ^ (prefixWord ++ tailWord_5560803).sum := by decide
  have hdescent : baseEnd_5560803 < baseStart_5560803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560816 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2]
def baseStart_5560816 : Nat := 118140960795 + 5560816 * 2 ^ 59
def prefixEnd_5560816 : Nat := 4983230072969 + 3 ^ 40 * 5560816 * 2
def baseEnd_5560816 : Nat := 2855371439212420515526279

theorem tailTrace_5560816 : CollatzResearch.WordTrace tailWord_5560816 prefixEnd_5560816 2855371439212420515526279 := by
  unfold tailWord_5560816
  simp only [CollatzResearch.WordTrace]
  refine ⟨101409810911060409303747151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135213081214747212404996201 101409810911060409303747151)
  ·
    refine ⟨152114716366590613955620727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101409810911060409303747151 152114716366590613955620727)
    ·
      refine ⟨228172074549885920933431091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152114716366590613955620727 228172074549885920933431091)
      ·
        refine ⟨342258111824828881400146637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228172074549885920933431091 342258111824828881400146637)
        ·
          refine ⟨128346791934310830525054989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342258111824828881400146637 128346791934310830525054989)
          ·
            refine ⟨48130046975366561446895621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128346791934310830525054989 48130046975366561446895621)
            ·
              refine ⟨9024383807881230271292929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48130046975366561446895621 9024383807881230271292929)
              ·
                refine ⟨6768287855910922703469697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9024383807881230271292929 6768287855910922703469697)
                ·
                  refine ⟨5076215891933192027602273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768287855910922703469697 5076215891933192027602273)
                  ·
                    refine ⟨3807161918949894020701705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076215891933192027602273 3807161918949894020701705)
                    ·
                      refine ⟨2855371439212420515526279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807161918949894020701705 2855371439212420515526279)
                      ·
                        rfl

theorem cell23_5560816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2].length) (baseStart_5560816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560816 prefixEnd_5560816 := by exact prefixLift 5560816
  have htrace : WordTrace (prefixWord ++ tailWord_5560816) baseStart_5560816 baseEnd_5560816 := by
    simpa [prefixWord, tailWord_5560816, baseEnd_5560816] using wordTrace_append hprefix tailTrace_5560816
  have hstable : (prefixWord ++ tailWord_5560816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560816).length < 2 ^ (prefixWord ++ tailWord_5560816).sum := by decide
  have hdescent : baseEnd_5560816 < baseStart_5560816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560822 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_5560822 : Nat := 118140960795 + 5560822 * 2 ^ 59
def prefixEnd_5560822 : Nat := 4983230072969 + 3 ^ 40 * 5560822 * 2
def baseEnd_5560822 : Nat := 317263835566260832450139

theorem tailTrace_5560822 : CollatzResearch.WordTrace tailWord_5560822 prefixEnd_5560822 317263835566260832450139 := by
  unfold tailWord_5560822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676240041256192602013295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135213227106732721088141813 12676240041256192602013295)
  ·
    refine ⟨19014360061884288903019943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12676240041256192602013295 19014360061884288903019943)
    ·
      refine ⟨28521540092826433354529915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19014360061884288903019943 28521540092826433354529915)
      ·
        refine ⟨42782310139239650031794873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28521540092826433354529915 42782310139239650031794873)
        ·
          refine ⟨32086732604429737523846155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42782310139239650031794873 32086732604429737523846155)
          ·
            refine ⟨48130098906644606285769233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32086732604429737523846155 48130098906644606285769233)
            ·
              refine ⟨36097574179983454714326925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48130098906644606285769233 36097574179983454714326925)
              ·
                refine ⟨13536590317493795517872597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36097574179983454714326925 13536590317493795517872597)
                ·
                  refine ⟨317263835566260832450139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13536590317493795517872597 317263835566260832450139)
                  ·
                    rfl

theorem cell23_5560822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_5560822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560822 prefixEnd_5560822 := by exact prefixLift 5560822
  have htrace : WordTrace (prefixWord ++ tailWord_5560822) baseStart_5560822 baseEnd_5560822 := by
    simpa [prefixWord, tailWord_5560822, baseEnd_5560822] using wordTrace_append hprefix tailTrace_5560822
  have hstable : (prefixWord ++ tailWord_5560822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560822).length < 2 ^ (prefixWord ++ tailWord_5560822).sum := by decide
  have hdescent : baseEnd_5560822 < baseStart_5560822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560835 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 7]
def baseStart_5560835 : Nat := 118140960795 + 5560835 * 2 ^ 59
def prefixEnd_5560835 : Nat := 4983230072969 + 3 ^ 40 * 5560835 * 2
def baseEnd_5560835 : Nat := 951793731781618647062897

theorem tailTrace_5560835 : CollatzResearch.WordTrace tailWord_5560835 prefixEnd_5560835 951793731781618647062897 := by
  unfold tailWord_5560835
  simp only [CollatzResearch.WordTrace]
  refine ⟨202820314809051984852435959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135213543206034656568290639 202820314809051984852435959)
  ·
    refine ⟨304230472213577977278653939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202820314809051984852435959 304230472213577977278653939)
    ·
      refine ⟨456345708320366965917980909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304230472213577977278653939 456345708320366965917980909)
      ·
        refine ⟨171129640620137612219242841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456345708320366965917980909 171129640620137612219242841)
        ·
          refine ⟨128347230465103209164432131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171129640620137612219242841 128347230465103209164432131)
          ·
            refine ⟨192520845697654813746648197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128347230465103209164432131 192520845697654813746648197)
            ·
              refine ⟨36097658568310277577496537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192520845697654813746648197 36097658568310277577496537)
              ·
                refine ⟨27073243926232708183122403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36097658568310277577496537 27073243926232708183122403)
                ·
                  refine ⟨40609865889349062274683605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27073243926232708183122403 40609865889349062274683605)
                  ·
                    refine ⟨951793731781618647062897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40609865889349062274683605 951793731781618647062897)
                    ·
                      rfl

theorem cell23_5560835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_5560835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560835 prefixEnd_5560835 := by exact prefixLift 5560835
  have htrace : WordTrace (prefixWord ++ tailWord_5560835) baseStart_5560835 baseEnd_5560835 := by
    simpa [prefixWord, tailWord_5560835, baseEnd_5560835] using wordTrace_append hprefix tailTrace_5560835
  have hstable : (prefixWord ++ tailWord_5560835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560835).length < 2 ^ (prefixWord ++ tailWord_5560835).sum := by decide
  have hdescent : baseEnd_5560835 < baseStart_5560835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560875 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_5560875 : Nat := 118140960795 + 5560875 * 2 ^ 59
def prefixEnd_5560875 : Nat := 4983230072969 + 3 ^ 40 * 5560875 * 2
def baseEnd_5560875 : Nat := 2855401734571035784688507

theorem tailTrace_5560875 : CollatzResearch.WordTrace tailWord_5560875 prefixEnd_5560875 2855401734571035784688507 := by
  unfold tailWord_5560875
  simp only [CollatzResearch.WordTrace]
  refine ⟨202821773728907071683892079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135214515819271381122594719 202821773728907071683892079)
  ·
    refine ⟨304232660593360607525838119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202821773728907071683892079 304232660593360607525838119)
    ·
      refine ⟨456348990890040911288757179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304232660593360607525838119 456348990890040911288757179)
      ·
        refine ⟨684523486335061366933135769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456348990890040911288757179 684523486335061366933135769)
        ·
          refine ⟨513392614751296025199851827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684523486335061366933135769 513392614751296025199851827)
          ·
            refine ⟨770088922126944037799777741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513392614751296025199851827 770088922126944037799777741)
            ·
              refine ⟨288783345797604014174916653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770088922126944037799777741 288783345797604014174916653)
              ·
                refine ⟨108293754674101505315593745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288783345797604014174916653 108293754674101505315593745)
                ·
                  refine ⟨81220316005576128986695309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108293754674101505315593745 81220316005576128986695309)
                  ·
                    refine ⟨30457618502091048370010741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81220316005576128986695309 30457618502091048370010741)
                    ·
                      refine ⟨2855401734571035784688507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30457618502091048370010741 2855401734571035784688507)
                      ·
                        rfl

theorem cell23_5560875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_5560875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560875 prefixEnd_5560875 := by exact prefixLift 5560875
  have htrace : WordTrace (prefixWord ++ tailWord_5560875) baseStart_5560875 baseEnd_5560875 := by
    simpa [prefixWord, tailWord_5560875, baseEnd_5560875] using wordTrace_append hprefix tailTrace_5560875
  have hstable : (prefixWord ++ tailWord_5560875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560875).length < 2 ^ (prefixWord ++ tailWord_5560875).sum := by decide
  have hdescent : baseEnd_5560875 < baseStart_5560875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560889 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5560889 : Nat := 118140960795 + 5560889 * 2 ^ 59
def prefixEnd_5560889 : Nat := 4983230072969 + 3 ^ 40 * 5560889 * 2
def baseEnd_5560889 : Nat := 2855408923300198729913443

theorem tailTrace_5560889 : CollatzResearch.WordTrace tailWord_5560889 prefixEnd_5560889 2855408923300198729913443 := by
  unfold tailWord_5560889
  simp only [CollatzResearch.WordTrace]
  refine ⟨202822284350856352074901721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135214856233904234716601147 202822284350856352074901721)
  ·
    refine ⟨152116713263142264056176291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202822284350856352074901721 152116713263142264056176291)
    ·
      refine ⟨228175069894713396084264437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152116713263142264056176291 228175069894713396084264437)
      ·
        refine ⟨21391412802629380882899791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228175069894713396084264437 21391412802629380882899791)
        ·
          refine ⟨32087119203944071324349687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21391412802629380882899791 32087119203944071324349687)
          ·
            refine ⟨48130678805916106986524531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32087119203944071324349687 48130678805916106986524531)
            ·
              refine ⟨72196018208874160479786797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48130678805916106986524531 72196018208874160479786797)
              ·
                refine ⟨27073506828327810179920049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72196018208874160479786797 27073506828327810179920049)
                ·
                  refine ⟨20305130121245857634940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27073506828327810179920049 20305130121245857634940037)
                  ·
                    refine ⟨3807211897733598306551257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20305130121245857634940037 3807211897733598306551257)
                    ·
                      refine ⟨2855408923300198729913443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807211897733598306551257 2855408923300198729913443)
                      ·
                        rfl

theorem cell23_5560889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5560889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560889 prefixEnd_5560889 := by exact prefixLift 5560889
  have htrace : WordTrace (prefixWord ++ tailWord_5560889) baseStart_5560889 baseEnd_5560889 := by
    simpa [prefixWord, tailWord_5560889, baseEnd_5560889] using wordTrace_append hprefix tailTrace_5560889
  have hstable : (prefixWord ++ tailWord_5560889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560889).length < 2 ^ (prefixWord ++ tailWord_5560889).sum := by decide
  have hdescent : baseEnd_5560889 < baseStart_5560889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560905 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_5560905 : Nat := 118140960795 + 5560905 * 2 ^ 59
def prefixEnd_5560905 : Nat := 4983230072969 + 3 ^ 40 * 5560905 * 2
def baseEnd_5560905 : Nat := 2855417138990670667313369

theorem tailTrace_5560905 : CollatzResearch.WordTrace tailWord_5560905 prefixEnd_5560905 2855417138990670667313369 := by
  unfold tailWord_5560905
  simp only [CollatzResearch.WordTrace]
  refine ⟨202822867918798386807484169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135215245279198924538322779 202822867918798386807484169)
  ·
    refine ⟨152117150939098790105613127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202822867918798386807484169 152117150939098790105613127)
    ·
      refine ⟨228175726408648185158419691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152117150939098790105613127 228175726408648185158419691)
      ·
        refine ⟨342263589612972277737629537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228175726408648185158419691 342263589612972277737629537)
        ·
          refine ⟨256697692209729208303222153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342263589612972277737629537 256697692209729208303222153)
          ·
            refine ⟨192523269157296906227416615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256697692209729208303222153 192523269157296906227416615)
            ·
              refine ⟨288784903735945359341124923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192523269157296906227416615 288784903735945359341124923)
              ·
                refine ⟨433177355603918039011687385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288784903735945359341124923 433177355603918039011687385)
                ·
                  refine ⟨324883016702938529258765539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433177355603918039011687385 324883016702938529258765539)
                  ·
                    refine ⟨487324525054407793888148309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324883016702938529258765539 487324525054407793888148309)
                    ·
                      refine ⟨2855417138990670667313369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 487324525054407793888148309 2855417138990670667313369)
                      ·
                        rfl

theorem cell23_5560905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_5560905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560905 prefixEnd_5560905 := by exact prefixLift 5560905
  have htrace : WordTrace (prefixWord ++ tailWord_5560905) baseStart_5560905 baseEnd_5560905 := by
    simpa [prefixWord, tailWord_5560905, baseEnd_5560905] using wordTrace_append hprefix tailTrace_5560905
  have hstable : (prefixWord ++ tailWord_5560905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560905).length < 2 ^ (prefixWord ++ tailWord_5560905).sum := by decide
  have hdescent : baseEnd_5560905 < baseStart_5560905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560933 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_5560933 : Nat := 118140960795 + 5560933 * 2 ^ 59
def prefixEnd_5560933 : Nat := 4983230072969 + 3 ^ 40 * 5560933 * 2
def baseEnd_5560933 : Nat := 951810505482998852587747

theorem tailTrace_5560933 : CollatzResearch.WordTrace tailWord_5560933 prefixEnd_5560933 951810505482998852587747 := by
  unfold tailWord_5560933
  simp only [CollatzResearch.WordTrace]
  refine ⟨202823889162696947589503453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135215926108464631726335635 202823889162696947589503453)
  ·
    refine ⟨76058958436011355346063795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202823889162696947589503453 76058958436011355346063795)
    ·
      refine ⟨114088437654017033019095693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76058958436011355346063795 114088437654017033019095693)
      ·
        refine ⟨42783164120256387382160885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114088437654017033019095693 42783164120256387382160885)
        ·
          refine ⟨4010921636274036317077583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42783164120256387382160885 4010921636274036317077583)
          ·
            refine ⟨6016382454411054475616375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010921636274036317077583 6016382454411054475616375)
            ·
              refine ⟨9024573681616581713424563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016382454411054475616375 9024573681616581713424563)
              ·
                refine ⟨13536860522424872570136845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024573681616581713424563 13536860522424872570136845)
                ·
                  refine ⟨5076322695909327213801317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13536860522424872570136845 5076322695909327213801317)
                  ·
                    refine ⟨951810505482998852587747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076322695909327213801317 951810505482998852587747)
                    ·
                      rfl

theorem cell23_5560933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_5560933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560933 prefixEnd_5560933 := by exact prefixLift 5560933
  have htrace : WordTrace (prefixWord ++ tailWord_5560933) baseStart_5560933 baseEnd_5560933 := by
    simpa [prefixWord, tailWord_5560933, baseEnd_5560933] using wordTrace_append hprefix tailTrace_5560933
  have hstable : (prefixWord ++ tailWord_5560933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560933).length < 2 ^ (prefixWord ++ tailWord_5560933).sum := by decide
  have hdescent : baseEnd_5560933 < baseStart_5560933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560939 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 3]
def baseStart_5560939 : Nat := 118140960795 + 5560939 * 2 ^ 59
def prefixEnd_5560939 : Nat := 4983230072969 + 3 ^ 40 * 5560939 * 2
def baseEnd_5560939 : Nat := 2855434597332923534288213

theorem tailTrace_5560939 : CollatzResearch.WordTrace tailWord_5560939 prefixEnd_5560939 2855434597332923534288213 := by
  unfold tailWord_5560939
  simp only [CollatzResearch.WordTrace]
  refine ⟨202824108000675210614221871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135216072000450140409481247 202824108000675210614221871)
  ·
    refine ⟨304236162001012815921332807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202824108000675210614221871 304236162001012815921332807)
    ·
      refine ⟨456354243001519223881999211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304236162001012815921332807 456354243001519223881999211)
      ·
        refine ⟨684531364502278835822998817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456354243001519223881999211 684531364502278835822998817)
        ·
          refine ⟨513398523376709126867249113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684531364502278835822998817 513398523376709126867249113)
          ·
            refine ⟨385048892532531845150436835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513398523376709126867249113 385048892532531845150436835)
            ·
              refine ⟨577573338798797767725655253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385048892532531845150436835 577573338798797767725655253)
              ·
                refine ⟨13536875128096822681070045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 577573338798797767725655253 13536875128096822681070045)
                ·
                  refine ⟨5076328173036308505401267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13536875128096822681070045 5076328173036308505401267)
                  ·
                    refine ⟨7614492259554462758101901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076328173036308505401267 7614492259554462758101901)
                    ·
                      refine ⟨2855434597332923534288213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614492259554462758101901 2855434597332923534288213)
                      ·
                        rfl

theorem cell23_5560939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 3].length) (baseStart_5560939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560939 prefixEnd_5560939 := by exact prefixLift 5560939
  have htrace : WordTrace (prefixWord ++ tailWord_5560939) baseStart_5560939 baseEnd_5560939 := by
    simpa [prefixWord, tailWord_5560939, baseEnd_5560939] using wordTrace_append hprefix tailTrace_5560939
  have hstable : (prefixWord ++ tailWord_5560939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560939).length < 2 ^ (prefixWord ++ tailWord_5560939).sum := by decide
  have hdescent : baseEnd_5560939 < baseStart_5560939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560989 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_5560989 : Nat := 118140960795 + 5560989 * 2 ^ 59
def prefixEnd_5560989 : Nat := 4983230072969 + 3 ^ 40 * 5560989 * 2
def baseEnd_5560989 : Nat := 951820090455216112887661

theorem tailTrace_5560989 : CollatzResearch.WordTrace tailWord_5560989 prefixEnd_5560989 951820090455216112887661 := by
  unfold tailWord_5560989
  simp only [CollatzResearch.WordTrace]
  refine ⟨202825931650494069153542021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135217287766996046102361347 202825931650494069153542021)
  ·
    refine ⟨38029862184467637966289129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202825931650494069153542021 38029862184467637966289129)
    ·
      refine ⟨28522396638350728474716847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38029862184467637966289129 28522396638350728474716847)
      ·
        refine ⟨42783594957526092712075271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28522396638350728474716847 42783594957526092712075271)
        ·
          refine ⟨64175392436289139068112907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42783594957526092712075271 64175392436289139068112907)
          ·
            refine ⟨96263088654433708602169361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64175392436289139068112907 96263088654433708602169361)
            ·
              refine ⟨72197316490825281451627021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96263088654433708602169361 72197316490825281451627021)
              ·
                refine ⟨27073993684059480544360133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72197316490825281451627021 27073993684059480544360133)
                ·
                  refine ⟨5076373815761152602067525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27073993684059480544360133 5076373815761152602067525)
                  ·
                    refine ⟨951820090455216112887661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076373815761152602067525 951820090455216112887661)
                    ·
                      rfl

theorem cell23_5560989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_5560989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560989 prefixEnd_5560989 := by exact prefixLift 5560989
  have htrace : WordTrace (prefixWord ++ tailWord_5560989) baseStart_5560989 baseEnd_5560989 := by
    simpa [prefixWord, tailWord_5560989, baseEnd_5560989] using wordTrace_append hprefix tailTrace_5560989
  have hstable : (prefixWord ++ tailWord_5560989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560989).length < 2 ^ (prefixWord ++ tailWord_5560989).sum := by decide
  have hdescent : baseEnd_5560989 < baseStart_5560989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5560990 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5560990 : Nat := 118140960795 + 5560990 * 2 ^ 59
def prefixEnd_5560990 : Nat := 4983230072969 + 3 ^ 40 * 5560990 * 2
def baseEnd_5560990 : Nat := 2855460784846302834750479

theorem tailTrace_5560990 : CollatzResearch.WordTrace tailWord_5560990 prefixEnd_5560990 2855460784846302834750479 := by
  unfold tailWord_5560990
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353246015436305790541053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135217312082326964216218949 25353246015436305790541053)
  ·
    refine ⟨9507467255788614671452895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25353246015436305790541053 9507467255788614671452895)
    ·
      refine ⟨14261200883682922007179343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9507467255788614671452895 14261200883682922007179343)
      ·
        refine ⟨21391801325524383010769015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261200883682922007179343 21391801325524383010769015)
        ·
          refine ⟨32087701988286574516153523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21391801325524383010769015 32087701988286574516153523)
          ·
            refine ⟨48131552982429861774230285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32087701988286574516153523 48131552982429861774230285)
            ·
              refine ⟨18049332368411198165336357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48131552982429861774230285 18049332368411198165336357)
              ·
                refine ⟨3384249819077099656000567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18049332368411198165336357 3384249819077099656000567)
                ·
                  refine ⟨5076374728615649484000851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384249819077099656000567 5076374728615649484000851)
                  ·
                    refine ⟨7614562092923474226001277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076374728615649484000851 7614562092923474226001277)
                    ·
                      refine ⟨2855460784846302834750479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614562092923474226001277 2855460784846302834750479)
                      ·
                        rfl

theorem cell23_5560990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5560990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5560990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5560990 prefixEnd_5560990 := by exact prefixLift 5560990
  have htrace : WordTrace (prefixWord ++ tailWord_5560990) baseStart_5560990 baseEnd_5560990 := by
    simpa [prefixWord, tailWord_5560990, baseEnd_5560990] using wordTrace_append hprefix tailTrace_5560990
  have hstable : (prefixWord ++ tailWord_5560990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5560990).length < 2 ^ (prefixWord ++ tailWord_5560990).sum := by decide
  have hdescent : baseEnd_5560990 < baseStart_5560990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5560990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561006 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5561006 : Nat := 118140960795 + 5561006 * 2 ^ 59
def prefixEnd_5561006 : Nat := 4983230072969 + 3 ^ 40 * 5561006 * 2
def baseEnd_5561006 : Nat := 951823000178924924050135

theorem tailTrace_5561006 : CollatzResearch.WordTrace tailWord_5561006 prefixEnd_5561006 951823000178924924050135 := by
  unfold tailWord_5561006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353318961429060132113859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135217701127621654037940581 25353318961429060132113859)
  ·
    refine ⟨38029978442143590198170789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25353318961429060132113859 38029978442143590198170789)
    ·
      refine ⟨7130620957901923162157023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38029978442143590198170789 7130620957901923162157023)
      ·
        refine ⟨10695931436852884743235535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130620957901923162157023 10695931436852884743235535)
        ·
          refine ⟨16043897155279327114853303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10695931436852884743235535 16043897155279327114853303)
          ·
            refine ⟨24065845732918990672279955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16043897155279327114853303 24065845732918990672279955)
            ·
              refine ⟨36098768599378486008419933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24065845732918990672279955 36098768599378486008419933)
              ·
                refine ⟨13537038224766932253157475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36098768599378486008419933 13537038224766932253157475)
                ·
                  refine ⟨20305557337150398379736213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13537038224766932253157475 20305557337150398379736213)
                  ·
                    refine ⟨951823000178924924050135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20305557337150398379736213 951823000178924924050135)
                    ·
                      rfl

theorem cell23_5561006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5561006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561006 prefixEnd_5561006 := by exact prefixLift 5561006
  have htrace : WordTrace (prefixWord ++ tailWord_5561006) baseStart_5561006 baseEnd_5561006 := by
    simpa [prefixWord, tailWord_5561006, baseEnd_5561006] using wordTrace_append hprefix tailTrace_5561006
  have hstable : (prefixWord ++ tailWord_5561006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561006).length < 2 ^ (prefixWord ++ tailWord_5561006).sum := by decide
  have hdescent : baseEnd_5561006 < baseStart_5561006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561013 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5561013 : Nat := 118140960795 + 5561013 * 2 ^ 59
def prefixEnd_5561013 : Nat := 4983230072969 + 3 ^ 40 * 5561013 * 2
def baseEnd_5561013 : Nat := 2855472594901356244762873

theorem tailTrace_5561013 : CollatzResearch.WordTrace tailWord_5561013 prefixEnd_5561013 2855472594901356244762873 := by
  unfold tailWord_5561013
  simp only [CollatzResearch.WordTrace]
  refine ⟨202826807002407121252415693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135217871334938080834943795 202826807002407121252415693)
  ·
    refine ⟨76060052625902670469655885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202826807002407121252415693 76060052625902670469655885)
    ·
      refine ⟨28522519734713501426120957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76060052625902670469655885 28522519734713501426120957)
      ·
        refine ⟨10695944900517563034795359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28522519734713501426120957 10695944900517563034795359)
        ·
          refine ⟨16043917350776344552193039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10695944900517563034795359 16043917350776344552193039)
          ·
            refine ⟨24065876026164516828289559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16043917350776344552193039 24065876026164516828289559)
            ·
              refine ⟨36098814039246775242434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24065876026164516828289559 36098814039246775242434339)
              ·
                refine ⟨54148221058870162863651509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36098814039246775242434339 54148221058870162863651509)
                ·
                  refine ⟨5076395724269077768467329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54148221058870162863651509 5076395724269077768467329)
                  ·
                    refine ⟨3807296793201808326350497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076395724269077768467329 3807296793201808326350497)
                    ·
                      refine ⟨2855472594901356244762873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807296793201808326350497 2855472594901356244762873)
                      ·
                        rfl

theorem cell23_5561013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5561013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561013 prefixEnd_5561013 := by exact prefixLift 5561013
  have htrace : WordTrace (prefixWord ++ tailWord_5561013) baseStart_5561013 baseEnd_5561013 := by
    simpa [prefixWord, tailWord_5561013, baseEnd_5561013] using wordTrace_append hprefix tailTrace_5561013
  have hstable : (prefixWord ++ tailWord_5561013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561013).length < 2 ^ (prefixWord ++ tailWord_5561013).sum := by decide
  have hdescent : baseEnd_5561013 < baseStart_5561013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561073 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_5561073 : Nat := 118140960795 + 5561073 * 2 ^ 59
def prefixEnd_5561073 : Nat := 4983230072969 + 3 ^ 40 * 5561073 * 2
def baseEnd_5561073 : Nat := 2855503403740626010012597

theorem tailTrace_5561073 : CollatzResearch.WordTrace tailWord_5561073 prefixEnd_5561073 2855503403740626010012597 := by
  unfold tailWord_5561073
  simp only [CollatzResearch.WordTrace]
  refine ⟨202828995382189751499599873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135219330254793167666399915 202828995382189751499599873)
  ·
    refine ⟨152121746536642313624699905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202828995382189751499599873 152121746536642313624699905)
    ·
      refine ⟨114091309902481735218524929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152121746536642313624699905 114091309902481735218524929)
      ·
        refine ⟨85568482426861301413893697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114091309902481735218524929 85568482426861301413893697)
        ·
          refine ⟨64176361820145976060420273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85568482426861301413893697 64176361820145976060420273)
          ·
            refine ⟨48132271365109482045315205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64176361820145976060420273 48132271365109482045315205)
            ·
              refine ⟨9024800880958027883496601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48132271365109482045315205 9024800880958027883496601)
              ·
                refine ⟨6768600660718520912622451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9024800880958027883496601 6768600660718520912622451)
                ·
                  refine ⟨10152900991077781368933677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768600660718520912622451 10152900991077781368933677)
                  ·
                    refine ⟨3807337871654168013350129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10152900991077781368933677 3807337871654168013350129)
                    ·
                      refine ⟨2855503403740626010012597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807337871654168013350129 2855503403740626010012597)
                      ·
                        rfl

theorem cell23_5561073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_5561073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561073 prefixEnd_5561073 := by exact prefixLift 5561073
  have htrace : WordTrace (prefixWord ++ tailWord_5561073) baseStart_5561073 baseEnd_5561073 := by
    simpa [prefixWord, tailWord_5561073, baseEnd_5561073] using wordTrace_append hprefix tailTrace_5561073
  have hstable : (prefixWord ++ tailWord_5561073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561073).length < 2 ^ (prefixWord ++ tailWord_5561073).sum := by decide
  have hdescent : baseEnd_5561073 < baseStart_5561073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561089 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_5561089 : Nat := 118140960795 + 5561089 * 2 ^ 59
def prefixEnd_5561089 : Nat := 4983230072969 + 3 ^ 40 * 5561089 * 2
def baseEnd_5561089 : Nat := 2855511619431097947412523

theorem tailTrace_5561089 : CollatzResearch.WordTrace tailWord_5561089 prefixEnd_5561089 2855511619431097947412523 := by
  unfold tailWord_5561089
  simp only [CollatzResearch.WordTrace]
  refine ⟨202829578950131786232182321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135219719300087857488121547 202829578950131786232182321)
  ·
    refine ⟨152122184212598839674136741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202829578950131786232182321 152122184212598839674136741)
    ·
      refine ⟨28522909539862282438900639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152122184212598839674136741 28522909539862282438900639)
      ·
        refine ⟨42784364309793423658350959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28522909539862282438900639 42784364309793423658350959)
        ·
          refine ⟨64176546464690135487526439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42784364309793423658350959 64176546464690135487526439)
          ·
            refine ⟨96264819697035203231289659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64176546464690135487526439 96264819697035203231289659)
            ·
              refine ⟨144397229545552804846934489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96264819697035203231289659 144397229545552804846934489)
              ·
                refine ⟨108297922159164603635200867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144397229545552804846934489 108297922159164603635200867)
                ·
                  refine ⟨162446883238746905452801301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108297922159164603635200867 162446883238746905452801301)
                  ·
                    refine ⟨7614697651816261193100061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 162446883238746905452801301 7614697651816261193100061)
                    ·
                      refine ⟨2855511619431097947412523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614697651816261193100061 2855511619431097947412523)
                      ·
                        rfl

theorem cell23_5561089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_5561089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561089 prefixEnd_5561089 := by exact prefixLift 5561089
  have htrace : WordTrace (prefixWord ++ tailWord_5561089) baseStart_5561089 baseEnd_5561089 := by
    simpa [prefixWord, tailWord_5561089, baseEnd_5561089] using wordTrace_append hprefix tailTrace_5561089
  have hstable : (prefixWord ++ tailWord_5561089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561089).length < 2 ^ (prefixWord ++ tailWord_5561089).sum := by decide
  have hdescent : baseEnd_5561089 < baseStart_5561089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561090 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_5561090 : Nat := 118140960795 + 5561090 * 2 ^ 59
def prefixEnd_5561090 : Nat := 4983230072969 + 3 ^ 40 * 5561090 * 2
def baseEnd_5561090 : Nat := 2855512132911752443500019

theorem tailTrace_5561090 : CollatzResearch.WordTrace tailWord_5561090 prefixEnd_5561090 2855512132911752443500019 := by
  unfold tailWord_5561090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50707403855782040850742181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135219743615418775601979149 50707403855782040850742181)
  ·
    refine ⟨9507638222959132659514159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50707403855782040850742181 9507638222959132659514159)
    ·
      refine ⟨14261457334438698989271239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9507638222959132659514159 14261457334438698989271239)
      ·
        refine ⟨21392186001658048483906859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261457334438698989271239 21392186001658048483906859)
        ·
          refine ⟨32088279002487072725860289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392186001658048483906859 32088279002487072725860289)
          ·
            refine ⟨24066209251865304544395217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32088279002487072725860289 24066209251865304544395217)
            ·
              refine ⟨18049656938898978408296413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24066209251865304544395217 18049656938898978408296413)
              ·
                refine ⟨6768621352087116903111155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18049656938898978408296413 6768621352087116903111155)
                ·
                  refine ⟨10152932028130675354666733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768621352087116903111155 10152932028130675354666733)
                  ·
                    refine ⟨3807349510549003258000025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10152932028130675354666733 3807349510549003258000025)
                    ·
                      refine ⟨2855512132911752443500019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807349510549003258000025 2855512132911752443500019)
                      ·
                        rfl

theorem cell23_5561090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_5561090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561090 prefixEnd_5561090 := by exact prefixLift 5561090
  have htrace : WordTrace (prefixWord ++ tailWord_5561090) baseStart_5561090 baseEnd_5561090 := by
    simpa [prefixWord, tailWord_5561090, baseEnd_5561090] using wordTrace_append hprefix tailTrace_5561090
  have hstable : (prefixWord ++ tailWord_5561090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561090).length < 2 ^ (prefixWord ++ tailWord_5561090).sum := by decide
  have hdescent : baseEnd_5561090 < baseStart_5561090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561103 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 2, 2, 2]
def baseStart_5561103 : Nat := 118140960795 + 5561103 * 2 ^ 59
def prefixEnd_5561103 : Nat := 4983230072969 + 3 ^ 40 * 5561103 * 2
def baseEnd_5561103 : Nat := 2855518808160260892637459

theorem tailTrace_5561103 : CollatzResearch.WordTrace tailWord_5561103 prefixEnd_5561103 2855518808160260892637459 := by
  unfold tailWord_5561103
  simp only [CollatzResearch.WordTrace]
  refine ⟨202830089572081066623191963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135220059714720711082127975 202830089572081066623191963)
  ·
    refine ⟨304245134358121599934787945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202830089572081066623191963 304245134358121599934787945)
    ·
      refine ⟨228183850768591199951090959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304245134358121599934787945 228183850768591199951090959)
      ·
        refine ⟨342275776152886799926636439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228183850768591199951090959 342275776152886799926636439)
        ·
          refine ⟨513413664229330199889954659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342275776152886799926636439 513413664229330199889954659)
          ·
            refine ⟨770120496343995299834931989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513413664229330199889954659 770120496343995299834931989)
            ·
              refine ⟨36099398266124779679762437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 770120496343995299834931989 36099398266124779679762437)
              ·
                refine ⟨6768637174898396189955457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36099398266124779679762437 6768637174898396189955457)
                ·
                  refine ⟨5076477881173797142466593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768637174898396189955457 5076477881173797142466593)
                  ·
                    refine ⟨3807358410880347856849945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076477881173797142466593 3807358410880347856849945)
                    ·
                      refine ⟨2855518808160260892637459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807358410880347856849945 2855518808160260892637459)
                      ·
                        rfl

theorem cell23_5561103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2, 2].length) (baseStart_5561103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561103 prefixEnd_5561103 := by exact prefixLift 5561103
  have htrace : WordTrace (prefixWord ++ tailWord_5561103) baseStart_5561103 baseEnd_5561103 := by
    simpa [prefixWord, tailWord_5561103, baseEnd_5561103] using wordTrace_append hprefix tailTrace_5561103
  have hstable : (prefixWord ++ tailWord_5561103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561103).length < 2 ^ (prefixWord ++ tailWord_5561103).sum := by decide
  have hdescent : baseEnd_5561103 < baseStart_5561103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561120 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5561120 : Nat := 118140960795 + 5561120 * 2 ^ 59
def prefixEnd_5561120 : Nat := 4983230072969 + 3 ^ 40 * 5561120 * 2
def baseEnd_5561120 : Nat := 2855527537331387326124881

theorem tailTrace_5561120 : CollatzResearch.WordTrace tailWord_5561120 prefixEnd_5561120 2855527537331387326124881 := by
  unfold tailWord_5561120
  simp only [CollatzResearch.WordTrace]
  refine ⟨101415354806509739263280407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135220473075346319017707209 101415354806509739263280407)
  ·
    refine ⟨152123032209764608894920611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101415354806509739263280407 152123032209764608894920611)
    ·
      refine ⟨228184548314646913342380917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152123032209764608894920611 228184548314646913342380917)
      ·
        refine ⟨21392301404498148125848211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228184548314646913342380917 21392301404498148125848211)
        ·
          refine ⟨32088452106747222188772317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392301404498148125848211 32088452106747222188772317)
          ·
            refine ⟨12033169540030208320789619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32088452106747222188772317 12033169540030208320789619)
            ·
              refine ⟨18049754310045312481184429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12033169540030208320789619 18049754310045312481184429)
              ·
                refine ⟨6768657866266992180444161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18049754310045312481184429 6768657866266992180444161)
                ·
                  refine ⟨5076493399700244135333121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768657866266992180444161 5076493399700244135333121)
                  ·
                    refine ⟨3807370049775183101499841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076493399700244135333121 3807370049775183101499841)
                    ·
                      refine ⟨2855527537331387326124881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807370049775183101499841 2855527537331387326124881)
                      ·
                        rfl

theorem cell23_5561120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5561120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561120 prefixEnd_5561120 := by exact prefixLift 5561120
  have htrace : WordTrace (prefixWord ++ tailWord_5561120) baseStart_5561120 baseEnd_5561120 := by
    simpa [prefixWord, tailWord_5561120, baseEnd_5561120] using wordTrace_append hprefix tailTrace_5561120
  have hstable : (prefixWord ++ tailWord_5561120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561120).length < 2 ^ (prefixWord ++ tailWord_5561120).sum := by decide
  have hdescent : baseEnd_5561120 < baseStart_5561120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561159 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5561159 : Nat := 118140960795 + 5561159 * 2 ^ 59
def prefixEnd_5561159 : Nat := 4983230072969 + 3 ^ 40 * 5561159 * 2
def baseEnd_5561159 : Nat := 2855547563076912673537201

theorem tailTrace_5561159 : CollatzResearch.WordTrace tailWord_5561159 prefixEnd_5561159 2855547563076912673537201 := by
  unfold tailWord_5561159
  simp only [CollatzResearch.WordTrace]
  refine ⟨202832132059878188187230531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135221421373252125458153687 202832132059878188187230531)
  ·
    refine ⟨304248198089817282280845797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202832132059878188187230531 304248198089817282280845797)
    ·
      refine ⟨57046537141840740427658587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304248198089817282280845797 57046537141840740427658587)
      ·
        refine ⟨85569805712761110641487881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57046537141840740427658587 85569805712761110641487881)
        ·
          refine ⟨64177354284570832981115911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85569805712761110641487881 64177354284570832981115911)
          ·
            refine ⟨96266031426856249471673867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64177354284570832981115911 96266031426856249471673867)
            ·
              refine ⟨144399047140284374207510801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96266031426856249471673867 144399047140284374207510801)
              ·
                refine ⟨108299285355213280655633101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144399047140284374207510801 108299285355213280655633101)
                ·
                  refine ⟨40612232008204980245862413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108299285355213280655633101 40612232008204980245862413)
                  ·
                    refine ⟨15229587003076867592198405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40612232008204980245862413 15229587003076867592198405)
                    ·
                      refine ⟨2855547563076912673537201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15229587003076867592198405 2855547563076912673537201)
                      ·
                        rfl

theorem cell23_5561159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5561159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561159 prefixEnd_5561159 := by exact prefixLift 5561159
  have htrace : WordTrace (prefixWord ++ tailWord_5561159) baseStart_5561159 baseEnd_5561159 := by
    simpa [prefixWord, tailWord_5561159, baseEnd_5561159] using wordTrace_append hprefix tailTrace_5561159
  have hstable : (prefixWord ++ tailWord_5561159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561159).length < 2 ^ (prefixWord ++ tailWord_5561159).sum := by decide
  have hdescent : baseEnd_5561159 < baseStart_5561159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3]
def baseStart_5561179 : Nat := 118140960795 + 5561179 * 2 ^ 59
def prefixEnd_5561179 : Nat := 4983230072969 + 3 ^ 40 * 5561179 * 2
def baseEnd_5561179 : Nat := 2855557832690002595287109

theorem tailTrace_5561179 : CollatzResearch.WordTrace tailWord_5561179 prefixEnd_5561179 2855557832690002595287109 := by
  unfold tailWord_5561179
  simp only [CollatzResearch.WordTrace]
  refine ⟨202832861519805731602958591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135221907679870487735305727 202832861519805731602958591)
  ·
    refine ⟨304249292279708597404437887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202832861519805731602958591 304249292279708597404437887)
    ·
      refine ⟨456373938419562896106656831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304249292279708597404437887 456373938419562896106656831)
      ·
        refine ⟨684560907629344344159985247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456373938419562896106656831 684560907629344344159985247)
        ·
          refine ⟨1026841361444016516239977871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684560907629344344159985247 1026841361444016516239977871)
          ·
            refine ⟨1540262042166024774359966807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026841361444016516239977871 1540262042166024774359966807)
            ·
              refine ⟨2310393063249037161539950211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540262042166024774359966807 2310393063249037161539950211)
              ·
                refine ⟨3465589594873555742309925317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310393063249037161539950211 3465589594873555742309925317)
                ·
                  refine ⟨649798049038791701683110997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3465589594873555742309925317 649798049038791701683110997)
                  ·
                    refine ⟨7614820887173340254098957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 649798049038791701683110997 7614820887173340254098957)
                    ·
                      refine ⟨2855557832690002595287109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614820887173340254098957 2855557832690002595287109)
                      ·
                        rfl

theorem cell23_5561179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].length) (baseStart_5561179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561179 prefixEnd_5561179 := by exact prefixLift 5561179
  have htrace : WordTrace (prefixWord ++ tailWord_5561179) baseStart_5561179 baseEnd_5561179 := by
    simpa [prefixWord, tailWord_5561179, baseEnd_5561179] using wordTrace_append hprefix tailTrace_5561179
  have hstable : (prefixWord ++ tailWord_5561179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561179).length < 2 ^ (prefixWord ++ tailWord_5561179).sum := by decide
  have hdescent : baseEnd_5561179 < baseStart_5561179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561196 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_5561196 : Nat := 118140960795 + 5561196 * 2 ^ 59
def prefixEnd_5561196 : Nat := 4983230072969 + 3 ^ 40 * 5561196 * 2
def baseEnd_5561196 : Nat := 2855566561861129028774531

theorem tailTrace_5561196 : CollatzResearch.WordTrace tailWord_5561196 prefixEnd_5561196 2855566561861129028774531 := by
  unfold tailWord_5561196
  simp only [CollatzResearch.WordTrace]
  refine ⟨101416740780372071753163721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135222321040496095670884961 101416740780372071753163721)
  ·
    refine ⟨76062555585279053814872791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101416740780372071753163721 76062555585279053814872791)
    ·
      refine ⟨114093833377918580722309187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76062555585279053814872791 114093833377918580722309187)
      ·
        refine ⟨171140750066877871083463781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114093833377918580722309187 171140750066877871083463781)
        ·
          refine ⟨32088890637539600828149459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171140750066877871083463781 32088890637539600828149459)
          ·
            refine ⟨48133335956309401242224189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32088890637539600828149459 48133335956309401242224189)
            ·
              refine ⟨18050000983616025465834071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48133335956309401242224189 18050000983616025465834071)
              ·
                refine ⟨27075001475424038198751107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18050000983616025465834071 27075001475424038198751107)
                ·
                  refine ⟨40612502213136057298126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27075001475424038198751107 40612502213136057298126661)
                  ·
                    refine ⟨7614844164963010743398749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40612502213136057298126661 7614844164963010743398749)
                    ·
                      refine ⟨2855566561861129028774531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614844164963010743398749 2855566561861129028774531)
                      ·
                        rfl

theorem cell23_5561196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_5561196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561196 prefixEnd_5561196 := by exact prefixLift 5561196
  have htrace : WordTrace (prefixWord ++ tailWord_5561196) baseStart_5561196 baseEnd_5561196 := by
    simpa [prefixWord, tailWord_5561196, baseEnd_5561196] using wordTrace_append hprefix tailTrace_5561196
  have hstable : (prefixWord ++ tailWord_5561196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561196).length < 2 ^ (prefixWord ++ tailWord_5561196).sum := by decide
  have hdescent : baseEnd_5561196 < baseStart_5561196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561203 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 1, 4]
def baseStart_5561203 : Nat := 118140960795 + 5561203 * 2 ^ 59
def prefixEnd_5561203 : Nat := 4983230072969 + 3 ^ 40 * 5561203 * 2
def baseEnd_5561203 : Nat := 951856718741903500462333

theorem tailTrace_5561203 : CollatzResearch.WordTrace tailWord_5561203 prefixEnd_5561203 951856718741903500462333 := by
  unfold tailWord_5561203
  simp only [CollatzResearch.WordTrace]
  refine ⟨202833736871718783701832263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135222491247812522467888175 202833736871718783701832263)
  ·
    refine ⟨304250605307578175552748395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202833736871718783701832263 304250605307578175552748395)
    ·
      refine ⟨456375907961367263329122593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304250605307578175552748395 456375907961367263329122593)
      ·
        refine ⟨342281930971025447496841945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456375907961367263329122593 342281930971025447496841945)
        ·
          refine ⟨256711448228269085622631459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342281930971025447496841945 256711448228269085622631459)
          ·
            refine ⟨385067172342403628433947189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256711448228269085622631459 385067172342403628433947189)
            ·
              refine ⟨36100047407100340165682549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 385067172342403628433947189 36100047407100340165682549)
              ·
                refine ⟨3384379444415656890532739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36100047407100340165682549 3384379444415656890532739)
                ·
                  refine ⟨5076569166623485335799109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384379444415656890532739 5076569166623485335799109)
                  ·
                    refine ⟨951856718741903500462333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076569166623485335799109 951856718741903500462333)
                    ·
                      rfl

theorem cell23_5561203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 4].length) (baseStart_5561203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561203 prefixEnd_5561203 := by exact prefixLift 5561203
  have htrace : WordTrace (prefixWord ++ tailWord_5561203) baseStart_5561203 baseEnd_5561203 := by
    simpa [prefixWord, tailWord_5561203, baseEnd_5561203] using wordTrace_append hprefix tailTrace_5561203
  have hstable : (prefixWord ++ tailWord_5561203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561203).length < 2 ^ (prefixWord ++ tailWord_5561203).sum := by decide
  have hdescent : baseEnd_5561203 < baseStart_5561203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561219 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_5561219 : Nat := 118140960795 + 5561219 * 2 ^ 59
def prefixEnd_5561219 : Nat := 4983230072969 + 3 ^ 40 * 5561219 * 2
def baseEnd_5561219 : Nat := 2855578371916182438786925

theorem tailTrace_5561219 : CollatzResearch.WordTrace tailWord_5561219 prefixEnd_5561219 2855578371916182438786925 := by
  unfold tailWord_5561219
  simp only [CollatzResearch.WordTrace]
  refine ⟨202834320439660818434414711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135222880293107212289609807 202834320439660818434414711)
  ·
    refine ⟨304251480659491227651622067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202834320439660818434414711 304251480659491227651622067)
    ·
      refine ⟨456377220989236841477433101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304251480659491227651622067 456377220989236841477433101)
      ·
        refine ⟨171141457870963815554037413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456377220989236841477433101 171141457870963815554037413)
        ·
          refine ⟨32089023350805715416382015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171141457870963815554037413 32089023350805715416382015)
          ·
            refine ⟨48133535026208573124573023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32089023350805715416382015 48133535026208573124573023)
            ·
              refine ⟨72200302539312859686859535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48133535026208573124573023 72200302539312859686859535)
              ·
                refine ⟨108300453808969289530289303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72200302539312859686859535 108300453808969289530289303)
                ·
                  refine ⟨162450680713453934295433955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108300453808969289530289303 162450680713453934295433955)
                  ·
                    refine ⟨243676021070180901443150933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162450680713453934295433955 243676021070180901443150933)
                    ·
                      refine ⟨2855578371916182438786925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 243676021070180901443150933 2855578371916182438786925)
                      ·
                        rfl

theorem cell23_5561219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_5561219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561219 prefixEnd_5561219 := by exact prefixLift 5561219
  have htrace : WordTrace (prefixWord ++ tailWord_5561219) baseStart_5561219 baseEnd_5561219 := by
    simpa [prefixWord, tailWord_5561219, baseEnd_5561219] using wordTrace_append hprefix tailTrace_5561219
  have hstable : (prefixWord ++ tailWord_5561219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561219).length < 2 ^ (prefixWord ++ tailWord_5561219).sum := by decide
  have hdescent : baseEnd_5561219 < baseStart_5561219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561236 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5561236 : Nat := 118140960795 + 5561236 * 2 ^ 59
def prefixEnd_5561236 : Nat := 4983230072969 + 3 ^ 40 * 5561236 * 2
def baseEnd_5561236 : Nat := 2855587101087308872274347

theorem tailTrace_5561236 : CollatzResearch.WordTrace tailWord_5561236 prefixEnd_5561236 2855587101087308872274347 := by
  unfold tailWord_5561236
  simp only [CollatzResearch.WordTrace]
  refine ⟨101417470240299615168891781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135223293653732820225189041 101417470240299615168891781)
  ·
    refine ⟨19015775670056177844167209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101417470240299615168891781 19015775670056177844167209)
    ·
      refine ⟨14261831752542133383125407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19015775670056177844167209 14261831752542133383125407)
      ·
        refine ⟨21392747628813200074688111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261831752542133383125407 21392747628813200074688111)
        ·
          refine ⟨32089121443219800112032167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392747628813200074688111 32089121443219800112032167)
          ·
            refine ⟨48133682164829700168048251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32089121443219800112032167 48133682164829700168048251)
            ·
              refine ⟨72200523247244550252072377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48133682164829700168048251 72200523247244550252072377)
              ·
                refine ⟨54150392435433412689054283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72200523247244550252072377 54150392435433412689054283)
                ·
                  refine ⟨81225588653150119033581425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54150392435433412689054283 81225588653150119033581425)
                  ·
                    refine ⟨60919191489862589275186069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81225588653150119033581425 60919191489862589275186069)
                    ·
                      refine ⟨2855587101087308872274347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60919191489862589275186069 2855587101087308872274347)
                      ·
                        rfl

theorem cell23_5561236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5561236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561236 prefixEnd_5561236 := by exact prefixLift 5561236
  have htrace : WordTrace (prefixWord ++ tailWord_5561236) baseStart_5561236 baseEnd_5561236 := by
    simpa [prefixWord, tailWord_5561236, baseEnd_5561236] using wordTrace_append hprefix tailTrace_5561236
  have hstable : (prefixWord ++ tailWord_5561236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561236).length < 2 ^ (prefixWord ++ tailWord_5561236).sum := by decide
  have hdescent : baseEnd_5561236 < baseStart_5561236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561266 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5561266 : Nat := 118140960795 + 5561266 * 2 ^ 59
def prefixEnd_5561266 : Nat := 4983230072969 + 3 ^ 40 * 5561266 * 2
def baseEnd_5561266 : Nat := 2855602505506943754899209

theorem tailTrace_5561266 : CollatzResearch.WordTrace tailWord_5561266 prefixEnd_5561266 2855602505506943754899209 := by
  unfold tailWord_5561266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50709008667622636365343913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135224023113660363640917101 50709008667622636365343913)
  ·
    refine ⟨38031756500716977274007935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50709008667622636365343913 38031756500716977274007935)
    ·
      refine ⟨57047634751075465911011903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38031756500716977274007935 57047634751075465911011903)
      ·
        refine ⟨85571452126613198866517855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57047634751075465911011903 85571452126613198866517855)
        ·
          refine ⟨128357178189919798299776783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85571452126613198866517855 128357178189919798299776783)
          ·
            refine ⟨192535767284879697449665175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128357178189919798299776783 192535767284879697449665175)
            ·
              refine ⟨288803650927319546174497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192535767284879697449665175 288803650927319546174497763)
              ·
                refine ⟨433205476390979319261746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288803650927319546174497763 433205476390979319261746645)
                ·
                  refine ⟨10153253352913577795197187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 433205476390979319261746645 10153253352913577795197187)
                  ·
                    refine ⟨15229880029370366692795781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10153253352913577795197187 15229880029370366692795781)
                    ·
                      refine ⟨2855602505506943754899209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15229880029370366692795781 2855602505506943754899209)
                      ·
                        rfl

theorem cell23_5561266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5561266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561266 prefixEnd_5561266 := by exact prefixLift 5561266
  have htrace : WordTrace (prefixWord ++ tailWord_5561266) baseStart_5561266 baseEnd_5561266 := by
    simpa [prefixWord, tailWord_5561266, baseEnd_5561266] using wordTrace_append hprefix tailTrace_5561266
  have hstable : (prefixWord ++ tailWord_5561266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561266).length < 2 ^ (prefixWord ++ tailWord_5561266).sum := by decide
  have hdescent : baseEnd_5561266 < baseStart_5561266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561277 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5561277 : Nat := 118140960795 + 5561277 * 2 ^ 59
def prefixEnd_5561277 : Nat := 4983230072969 + 3 ^ 40 * 5561277 * 2
def baseEnd_5561277 : Nat := 2855608153794143211861659

theorem tailTrace_5561277 : CollatzResearch.WordTrace tailWord_5561277 prefixEnd_5561277 2855608153794143211861659 := by
  unfold tailWord_5561277
  simp only [CollatzResearch.WordTrace]
  refine ⟨202836435873450694340026085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135224290582300462893350723 202836435873450694340026085)
  ·
    refine ⟨38031831726272005188754891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202836435873450694340026085 38031831726272005188754891)
    ·
      refine ⟨57047747589408007783132337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38031831726272005188754891 57047747589408007783132337)
      ·
        refine ⟨42785810692056005837349253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57047747589408007783132337 42785810692056005837349253)
        ·
          refine ⟨8022339504760501094502985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42785810692056005837349253 8022339504760501094502985)
          ·
            refine ⟨6016754628570375820877239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022339504760501094502985 6016754628570375820877239)
            ·
              refine ⟨9025131942855563731315859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016754628570375820877239 9025131942855563731315859)
              ·
                refine ⟨13537697914283345596973789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025131942855563731315859 13537697914283345596973789)
                ·
                  refine ⟨5076636717856254598865171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13537697914283345596973789 5076636717856254598865171)
                  ·
                    refine ⟨7614955076784381898297757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076636717856254598865171 7614955076784381898297757)
                    ·
                      refine ⟨2855608153794143211861659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614955076784381898297757 2855608153794143211861659)
                      ·
                        rfl

theorem cell23_5561277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5561277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561277 prefixEnd_5561277 := by exact prefixLift 5561277
  have htrace : WordTrace (prefixWord ++ tailWord_5561277) baseStart_5561277 baseEnd_5561277 := by
    simpa [prefixWord, tailWord_5561277, baseEnd_5561277] using wordTrace_append hprefix tailTrace_5561277
  have hstable : (prefixWord ++ tailWord_5561277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561277).length < 2 ^ (prefixWord ++ tailWord_5561277).sum := by decide
  have hdescent : baseEnd_5561277 < baseStart_5561277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561284 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 6]
def baseStart_5561284 : Nat := 118140960795 + 5561284 * 2 ^ 59
def prefixEnd_5561284 : Nat := 4983230072969 + 3 ^ 40 * 5561284 * 2
def baseEnd_5561284 : Nat := 317290194239858298274903

theorem tailTrace_5561284 : CollatzResearch.WordTrace tailWord_5561284 prefixEnd_5561284 317290194239858298274903 := by
  unfold tailWord_5561284
  simp only [CollatzResearch.WordTrace]
  refine ⟨101418345592212667267765453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135224460789616889690353937 101418345592212667267765453)
  ·
    refine ⟨38031879597079750225412045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101418345592212667267765453 38031879597079750225412045)
    ·
      refine ⟨14261954848904906334529517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38031879597079750225412045 14261954848904906334529517)
      ·
        refine ⟨5348233068339339875448569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14261954848904906334529517 5348233068339339875448569)
        ·
          refine ⟨4011174801254504906586427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348233068339339875448569 4011174801254504906586427)
          ·
            refine ⟨6016762201881757359879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011174801254504906586427 6016762201881757359879641)
            ·
              refine ⟨4512571651411318019909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6016762201881757359879641 4512571651411318019909731)
              ·
                refine ⟨6768857477116977029864597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512571651411318019909731 6768857477116977029864597)
                ·
                  refine ⟨317290194239858298274903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6768857477116977029864597 317290194239858298274903)
                  ·
                    rfl

theorem cell23_5561284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_5561284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561284 prefixEnd_5561284 := by exact prefixLift 5561284
  have htrace : WordTrace (prefixWord ++ tailWord_5561284) baseStart_5561284 baseEnd_5561284 := by
    simpa [prefixWord, tailWord_5561284, baseEnd_5561284] using wordTrace_append hprefix tailTrace_5561284
  have hstable : (prefixWord ++ tailWord_5561284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561284).length < 2 ^ (prefixWord ++ tailWord_5561284).sum := by decide
  have hdescent : baseEnd_5561284 < baseStart_5561284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561296 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_5561296 : Nat := 118140960795 + 5561296 * 2 ^ 59
def prefixEnd_5561296 : Nat := 4983230072969 + 3 ^ 40 * 5561296 * 2
def baseEnd_5561296 : Nat := 2855617909926578637524071

theorem tailTrace_5561296 : CollatzResearch.WordTrace tailWord_5561296 prefixEnd_5561296 2855617909926578637524071 := by
  unfold tailWord_5561296
  simp only [CollatzResearch.WordTrace]
  refine ⟨101418564430190930292483871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135224752573587907056645161 101418564430190930292483871)
  ·
    refine ⟨152127846645286395438725807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101418564430190930292483871 152127846645286395438725807)
    ·
      refine ⟨228191769967929593158088711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152127846645286395438725807 228191769967929593158088711)
      ·
        refine ⟨342287654951894389737133067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228191769967929593158088711 342287654951894389737133067)
        ·
          refine ⟨513431482427841584605699601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342287654951894389737133067 513431482427841584605699601)
          ·
            refine ⟨385073611820881188454274701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513431482427841584605699601 385073611820881188454274701)
            ·
              refine ⟨144402604432830445670353013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385073611820881188454274701 144402604432830445670353013)
              ·
                refine ⟨13537744165577854281595595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144402604432830445670353013 13537744165577854281595595)
                ·
                  refine ⟨20306616248366781422393393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13537744165577854281595595 20306616248366781422393393)
                  ·
                    refine ⟨15229962186275086066795045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20306616248366781422393393 15229962186275086066795045)
                    ·
                      refine ⟨2855617909926578637524071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15229962186275086066795045 2855617909926578637524071)
                      ·
                        rfl

theorem cell23_5561296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_5561296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561296 prefixEnd_5561296 := by exact prefixLift 5561296
  have htrace : WordTrace (prefixWord ++ tailWord_5561296) baseStart_5561296 baseEnd_5561296 := by
    simpa [prefixWord, tailWord_5561296, baseEnd_5561296] using wordTrace_append hprefix tailTrace_5561296
  have hstable : (prefixWord ++ tailWord_5561296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561296).length < 2 ^ (prefixWord ++ tailWord_5561296).sum := by decide
  have hdescent : baseEnd_5561296 < baseStart_5561296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561300 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5561300 : Nat := 118140960795 + 5561300 * 2 ^ 59
def prefixEnd_5561300 : Nat := 4983230072969 + 3 ^ 40 * 5561300 * 2
def baseEnd_5561300 : Nat := 2855619963849196621874053

theorem tailTrace_5561300 : CollatzResearch.WordTrace tailWord_5561300 prefixEnd_5561300 2855619963849196621874053 := by
  unfold tailWord_5561300
  simp only [CollatzResearch.WordTrace]
  refine ⟨101418637376183684634056677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135224849834911579512075569 101418637376183684634056677)
  ·
    refine ⟨19015994508034440868885627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101418637376183684634056677 19015994508034440868885627)
    ·
      refine ⟨28523991762051661303328441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19015994508034440868885627 28523991762051661303328441)
      ·
        refine ⟨21392993821538745977496331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28523991762051661303328441 21392993821538745977496331)
        ·
          refine ⟨32089490732308118966244497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392993821538745977496331 32089490732308118966244497)
          ·
            refine ⟨24067118049231089224683373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32089490732308118966244497 24067118049231089224683373)
            ·
              refine ⟨9025169268461658459256265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24067118049231089224683373 9025169268461658459256265)
              ·
                refine ⟨6768876951346243844442199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9025169268461658459256265 6768876951346243844442199)
                ·
                  refine ⟨10153315427019365766663299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768876951346243844442199 10153315427019365766663299)
                  ·
                    refine ⟨15229973140529048649994949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10153315427019365766663299 15229973140529048649994949)
                    ·
                      refine ⟨2855619963849196621874053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15229973140529048649994949 2855619963849196621874053)
                      ·
                        rfl

theorem cell23_5561300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5561300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561300 prefixEnd_5561300 := by exact prefixLift 5561300
  have htrace : WordTrace (prefixWord ++ tailWord_5561300) baseStart_5561300 baseEnd_5561300 := by
    simpa [prefixWord, tailWord_5561300, baseEnd_5561300] using wordTrace_append hprefix tailTrace_5561300
  have hstable : (prefixWord ++ tailWord_5561300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561300).length < 2 ^ (prefixWord ++ tailWord_5561300).sum := by decide
  have hdescent : baseEnd_5561300 < baseStart_5561300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561303 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_5561303 : Nat := 118140960795 + 5561303 * 2 ^ 59
def prefixEnd_5561303 : Nat := 4983230072969 + 3 ^ 40 * 5561303 * 2
def baseEnd_5561303 : Nat := 2855621504291160110136539

theorem tailTrace_5561303 : CollatzResearch.WordTrace tailWord_5561303 prefixEnd_5561303 2855621504291160110136539 := by
  unfold tailWord_5561303
  simp only [CollatzResearch.WordTrace]
  refine ⟨202837384171356500780472563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135224922780904333853648375 202837384171356500780472563)
  ·
    refine ⟨304256076257034751170708845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202837384171356500780472563 304256076257034751170708845)
    ·
      refine ⟨114096028596388031689015817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304256076257034751170708845 114096028596388031689015817)
      ·
        refine ⟨85572021447291023766761863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114096028596388031689015817 85572021447291023766761863)
        ·
          refine ⟨128358032170936535650142795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85572021447291023766761863 128358032170936535650142795)
          ·
            refine ⟨192537048256404803475214193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128358032170936535650142795 192537048256404803475214193)
            ·
              refine ⟨144402786192303602606410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192537048256404803475214193 144402786192303602606410645)
              ·
                refine ⟨6768880602764231372175499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144402786192303602606410645 6768880602764231372175499)
                ·
                  refine ⟨10153320904146347058263249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768880602764231372175499 10153320904146347058263249)
                  ·
                    refine ⟨7614990678109760293697437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10153320904146347058263249 7614990678109760293697437)
                    ·
                      refine ⟨2855621504291160110136539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7614990678109760293697437 2855621504291160110136539)
                      ·
                        rfl

theorem cell23_5561303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_5561303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561303 prefixEnd_5561303 := by exact prefixLift 5561303
  have htrace : WordTrace (prefixWord ++ tailWord_5561303) baseStart_5561303 baseEnd_5561303 := by
    simpa [prefixWord, tailWord_5561303, baseEnd_5561303] using wordTrace_append hprefix tailTrace_5561303
  have hstable : (prefixWord ++ tailWord_5561303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561303).length < 2 ^ (prefixWord ++ tailWord_5561303).sum := by decide
  have hdescent : baseEnd_5561303 < baseStart_5561303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561306 : List Nat := [3, 1, 1, 2, 4, 1, 2, 9]
def baseStart_5561306 : Nat := 118140960795 + 5561306 * 2 ^ 59
def prefixEnd_5561306 : Nat := 4983230072969 + 3 ^ 40 * 5561306 * 2
def baseEnd_5561306 : Nat := 105763816471597170311075

theorem tailTrace_5561306 : CollatzResearch.WordTrace tailWord_5561306 prefixEnd_5561306 105763816471597170311075 := by
  unfold tailWord_5561306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50709373397586408073207943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135224995726897088195221181 50709373397586408073207943)
  ·
    refine ⟨76064060096379612109811915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50709373397586408073207943 76064060096379612109811915)
    ·
      refine ⟨114096090144569418164717873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76064060096379612109811915 114096090144569418164717873)
      ·
        refine ⟨85572067608427063623538405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114096090144569418164717873 85572067608427063623538405)
        ·
          refine ⟨16044762676580074429413451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85572067608427063623538405 16044762676580074429413451)
          ·
            refine ⟨24067144014870111644120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16044762676580074429413451 24067144014870111644120177)
            ·
              refine ⟨18050358011152583733090133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24067144014870111644120177 18050358011152583733090133)
              ·
                refine ⟨105763816471597170311075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18050358011152583733090133 105763816471597170311075)
                ·
                  rfl

theorem cell23_5561306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_5561306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561306 prefixEnd_5561306 := by exact prefixLift 5561306
  have htrace : WordTrace (prefixWord ++ tailWord_5561306) baseStart_5561306 baseEnd_5561306 := by
    simpa [prefixWord, tailWord_5561306, baseEnd_5561306] using wordTrace_append hprefix tailTrace_5561306
  have hstable : (prefixWord ++ tailWord_5561306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561306).length < 2 ^ (prefixWord ++ tailWord_5561306).sum := by decide
  have hdescent : baseEnd_5561306 < baseStart_5561306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561377 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5561377 : Nat := 118140960795 + 5561377 * 2 ^ 59
def prefixEnd_5561377 : Nat := 4983230072969 + 3 ^ 40 * 5561377 * 2
def baseEnd_5561377 : Nat := 2855659501859592820611199

theorem tailTrace_5561377 : CollatzResearch.WordTrace tailWord_5561377 prefixEnd_5561377 2855659501859592820611199 := by
  unfold tailWord_5561377
  simp only [CollatzResearch.WordTrace]
  refine ⟨202840083173088411418666385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135226722115392274279110923 202840083173088411418666385)
  ·
    refine ⟨152130062379816308563999789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202840083173088411418666385 152130062379816308563999789)
    ·
      refine ⟨57048773392431115711499921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152130062379816308563999789 57048773392431115711499921)
      ·
        refine ⟨42786580044323336783624941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57048773392431115711499921 42786580044323336783624941)
        ·
          refine ⟨16044967516621251293859353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42786580044323336783624941 16044967516621251293859353)
          ·
            refine ⟨12033725637465938470394515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16044967516621251293859353 12033725637465938470394515)
            ·
              refine ⟨18050588456198907705591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12033725637465938470394515 18050588456198907705591773)
              ·
                refine ⟨6768970671074590389596915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18050588456198907705591773 6768970671074590389596915)
                ·
                  refine ⟨10153456006611885584395373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768970671074590389596915 10153456006611885584395373)
                  ·
                    refine ⟨3807546002479457094148265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10153456006611885584395373 3807546002479457094148265)
                    ·
                      refine ⟨2855659501859592820611199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807546002479457094148265 2855659501859592820611199)
                      ·
                        rfl

theorem cell23_5561377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5561377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561377 prefixEnd_5561377 := by exact prefixLift 5561377
  have htrace : WordTrace (prefixWord ++ tailWord_5561377) baseStart_5561377 baseEnd_5561377 := by
    simpa [prefixWord, tailWord_5561377, baseEnd_5561377] using wordTrace_append hprefix tailTrace_5561377
  have hstable : (prefixWord ++ tailWord_5561377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561377).length < 2 ^ (prefixWord ++ tailWord_5561377).sum := by decide
  have hdescent : baseEnd_5561377 < baseStart_5561377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561447 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 5]
def baseStart_5561447 : Nat := 118140960795 + 5561447 * 2 ^ 59
def prefixEnd_5561447 : Nat := 4983230072969 + 3 ^ 40 * 5561447 * 2
def baseEnd_5561447 : Nat := 317299493945045282970653

theorem tailTrace_5561447 : CollatzResearch.WordTrace tailWord_5561447 prefixEnd_5561447 317299493945045282970653 := by
  unfold tailWord_5561447
  simp only [CollatzResearch.WordTrace]
  refine ⟨202842636282834813373714595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135228424188556542249143063 202842636282834813373714595)
  ·
    refine ⟨304263954424252220060571893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202842636282834813373714595 304263954424252220060571893)
    ·
      refine ⟨28524745727273645630678615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304263954424252220060571893 28524745727273645630678615)
      ·
        refine ⟨42787118590910468446017923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28524745727273645630678615 42787118590910468446017923)
        ·
          refine ⟨64180677886365702669026885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42787118590910468446017923 64180677886365702669026885)
          ·
            refine ⟨12033877103693569250442541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64180677886365702669026885 12033877103693569250442541)
            ·
              refine ⟨4512703913885088468915953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12033877103693569250442541 4512703913885088468915953)
              ·
                refine ⟨3384527935413816351686965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4512703913885088468915953 3384527935413816351686965)
                ·
                  refine ⟨317299493945045282970653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384527935413816351686965 317299493945045282970653)
                  ·
                    rfl

theorem cell23_5561447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 5].length) (baseStart_5561447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561447 prefixEnd_5561447 := by exact prefixLift 5561447
  have htrace : WordTrace (prefixWord ++ tailWord_5561447) baseStart_5561447 baseEnd_5561447 := by
    simpa [prefixWord, tailWord_5561447, baseEnd_5561447] using wordTrace_append hprefix tailTrace_5561447
  have hstable : (prefixWord ++ tailWord_5561447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561447).length < 2 ^ (prefixWord ++ tailWord_5561447).sum := by decide
  have hdescent : baseEnd_5561447 < baseStart_5561447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561453 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5561453 : Nat := 118140960795 + 5561453 * 2 ^ 59
def prefixEnd_5561453 : Nat := 4983230072969 + 3 ^ 40 * 5561453 * 2
def baseEnd_5561453 : Nat := 2855698526389334523260849

theorem tailTrace_5561453 : CollatzResearch.WordTrace tailWord_5561453 prefixEnd_5561453 2855698526389334523260849 := by
  unfold tailWord_5561453
  simp only [CollatzResearch.WordTrace]
  refine ⟨202842855120813076398433013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135228570080542050932288675 202842855120813076398433013)
  ·
    refine ⟨19016517667576225912353095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202842855120813076398433013 19016517667576225912353095)
    ·
      refine ⟨28524776501364338868529643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19016517667576225912353095 28524776501364338868529643)
      ·
        refine ⟨42787164752046508302794465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28524776501364338868529643 42787164752046508302794465)
        ·
          refine ⟨32090373564034881227095849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42787164752046508302794465 32090373564034881227095849)
          ·
            refine ⟨24067780173026160920321887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32090373564034881227095849 24067780173026160920321887)
            ·
              refine ⟨36101670259539241380482831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24067780173026160920321887 36101670259539241380482831)
              ·
                refine ⟨54152505389308862070724247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36101670259539241380482831 54152505389308862070724247)
                ·
                  refine ⟨81228758083963293106086371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54152505389308862070724247 81228758083963293106086371)
                  ·
                    refine ⟨121843137125944939659129557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81228758083963293106086371 121843137125944939659129557)
                    ·
                      refine ⟨2855698526389334523260849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121843137125944939659129557 2855698526389334523260849)
                      ·
                        rfl

theorem cell23_5561453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5561453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561453 prefixEnd_5561453 := by exact prefixLift 5561453
  have htrace : WordTrace (prefixWord ++ tailWord_5561453) baseStart_5561453 baseEnd_5561453 := by
    simpa [prefixWord, tailWord_5561453, baseEnd_5561453] using wordTrace_append hprefix tailTrace_5561453
  have hstable : (prefixWord ++ tailWord_5561453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561453).length < 2 ^ (prefixWord ++ tailWord_5561453).sum := by decide
  have hdescent : baseEnd_5561453 < baseStart_5561453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561463 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_5561463 : Nat := 118140960795 + 5561463 * 2 ^ 59
def prefixEnd_5561463 : Nat := 4983230072969 + 3 ^ 40 * 5561463 * 2
def baseEnd_5561463 : Nat := 2855703661195879484135803

theorem tailTrace_5561463 : CollatzResearch.WordTrace tailWord_5561463 prefixEnd_5561463 2855703661195879484135803 := by
  unfold tailWord_5561463
  simp only [CollatzResearch.WordTrace]
  refine ⟨202843219850776848106297043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135228813233851232070864695 202843219850776848106297043)
  ·
    refine ⟨304264829776165272159445565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202843219850776848106297043 304264829776165272159445565)
    ·
      refine ⟨114099311166061977059792087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304264829776165272159445565 114099311166061977059792087)
      ·
        refine ⟨171148966749092965589688131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114099311166061977059792087 171148966749092965589688131)
        ·
          refine ⟨256723450123639448384532197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171148966749092965589688131 256723450123639448384532197)
          ·
            refine ⟨48135646898182396572099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256723450123639448384532197 48135646898182396572099787)
            ·
              refine ⟨72203470347273594858149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48135646898182396572099787 72203470347273594858149681)
              ·
                refine ⟨54152602760455196143612261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72203470347273594858149681 54152602760455196143612261)
                ·
                  refine ⟨10153613017585349276927299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54152602760455196143612261 10153613017585349276927299)
                  ·
                    refine ⟨15230419526378023915390949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10153613017585349276927299 15230419526378023915390949)
                    ·
                      refine ⟨2855703661195879484135803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15230419526378023915390949 2855703661195879484135803)
                      ·
                        rfl

theorem cell23_5561463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_5561463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561463 prefixEnd_5561463 := by exact prefixLift 5561463
  have htrace : WordTrace (prefixWord ++ tailWord_5561463) baseStart_5561463 baseEnd_5561463 := by
    simpa [prefixWord, tailWord_5561463, baseEnd_5561463] using wordTrace_append hprefix tailTrace_5561463
  have hstable : (prefixWord ++ tailWord_5561463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561463).length < 2 ^ (prefixWord ++ tailWord_5561463).sum := by decide
  have hdescent : baseEnd_5561463 < baseStart_5561463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561483 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3]
def baseStart_5561483 : Nat := 118140960795 + 5561483 * 2 ^ 59
def prefixEnd_5561483 : Nat := 4983230072969 + 3 ^ 40 * 5561483 * 2
def baseEnd_5561483 : Nat := 2855713930808969405885711

theorem tailTrace_5561483 : CollatzResearch.WordTrace tailWord_5561483 prefixEnd_5561483 2855713930808969405885711 := by
  unfold tailWord_5561483
  simp only [CollatzResearch.WordTrace]
  refine ⟨202843949310704391522025103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135229299540469594348016735 202843949310704391522025103)
  ·
    refine ⟨304265923966056587283037655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202843949310704391522025103 304265923966056587283037655)
    ·
      refine ⟨456398885949084880924556483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304265923966056587283037655 456398885949084880924556483)
      ·
        refine ⟨684598328923627321386834725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456398885949084880924556483 684598328923627321386834725)
        ·
          refine ⟨128362186673180122760031511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 684598328923627321386834725 128362186673180122760031511)
          ·
            refine ⟨192543280009770184140047267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128362186673180122760031511 192543280009770184140047267)
            ·
              refine ⟨288814920014655276210070901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192543280009770184140047267 288814920014655276210070901)
              ·
                refine ⟨27076398751373932144694147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288814920014655276210070901 27076398751373932144694147)
                ·
                  refine ⟨40614598127060898217041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27076398751373932144694147 40614598127060898217041221)
                  ·
                    refine ⟨7615237148823918415695229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40614598127060898217041221 7615237148823918415695229)
                    ·
                      refine ⟨2855713930808969405885711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615237148823918415695229 2855713930808969405885711)
                      ·
                        rfl

theorem cell23_5561483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].length) (baseStart_5561483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561483 prefixEnd_5561483 := by exact prefixLift 5561483
  have htrace : WordTrace (prefixWord ++ tailWord_5561483) baseStart_5561483 baseEnd_5561483 := by
    simpa [prefixWord, tailWord_5561483, baseEnd_5561483] using wordTrace_append hprefix tailTrace_5561483
  have hstable : (prefixWord ++ tailWord_5561483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561483).length < 2 ^ (prefixWord ++ tailWord_5561483).sum := by decide
  have hdescent : baseEnd_5561483 < baseStart_5561483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561514 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5561514 : Nat := 118140960795 + 5561514 * 2 ^ 59
def prefixEnd_5561514 : Nat := 4983230072969 + 3 ^ 40 * 5561514 * 2
def baseEnd_5561514 : Nat := 2855729848709258784598069

theorem tailTrace_5561514 : CollatzResearch.WordTrace tailWord_5561514 prefixEnd_5561514 2855729848709258784598069 := by
  unfold tailWord_5561514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50711269993398020954100899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135230053315728055877602397 50711269993398020954100899)
  ·
    refine ⟨76066904990097031431151349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50711269993398020954100899 76066904990097031431151349)
    ·
      refine ⟨7131272342821596696670439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76066904990097031431151349 7131272342821596696670439)
      ·
        refine ⟨10696908514232395045005659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131272342821596696670439 10696908514232395045005659)
        ·
          refine ⟨16045362771348592567508489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10696908514232395045005659 16045362771348592567508489)
          ·
            refine ⟨12034022078511444425631367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16045362771348592567508489 12034022078511444425631367)
            ·
              refine ⟨18051033117767166638447051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034022078511444425631367 18051033117767166638447051)
              ·
                refine ⟨27076549676650749957670577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18051033117767166638447051 27076549676650749957670577)
                ·
                  refine ⟨20307412257488062468252933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27076549676650749957670577 20307412257488062468252933)
                  ·
                    refine ⟨3807639798279011712797425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20307412257488062468252933 3807639798279011712797425)
                    ·
                      refine ⟨2855729848709258784598069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807639798279011712797425 2855729848709258784598069)
                      ·
                        rfl

theorem cell23_5561514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5561514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561514 prefixEnd_5561514 := by exact prefixLift 5561514
  have htrace : WordTrace (prefixWord ++ tailWord_5561514) baseStart_5561514 baseEnd_5561514 := by
    simpa [prefixWord, tailWord_5561514, baseEnd_5561514] using wordTrace_append hprefix tailTrace_5561514
  have hstable : (prefixWord ++ tailWord_5561514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561514).length < 2 ^ (prefixWord ++ tailWord_5561514).sum := by decide
  have hdescent : baseEnd_5561514 < baseStart_5561514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561534 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_5561534 : Nat := 118140960795 + 5561534 * 2 ^ 59
def prefixEnd_5561534 : Nat := 4983230072969 + 3 ^ 40 * 5561534 * 2
def baseEnd_5561534 : Nat := 2855740118322348706347977

theorem tailTrace_5561534 : CollatzResearch.WordTrace tailWord_5561534 prefixEnd_5561534 2855740118322348706347977 := by
  unfold tailWord_5561534
  simp only [CollatzResearch.WordTrace]
  refine ⟨25355726179189953404016457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135230539622346418154754437 25355726179189953404016457)
  ·
    refine ⟨19016794634392465053012343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25355726179189953404016457 19016794634392465053012343)
    ·
      refine ⟨28525191951588697579518515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19016794634392465053012343 28525191951588697579518515)
      ·
        refine ⟨42787787927383046369277773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28525191951588697579518515 42787787927383046369277773)
        ·
          refine ⟨16045420472768642388479165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42787787927383046369277773 16045420472768642388479165)
          ·
            refine ⟨6017032677288240895679687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16045420472768642388479165 6017032677288240895679687)
            ·
              refine ⟨9025549015932361343519531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017032677288240895679687 9025549015932361343519531)
              ·
                refine ⟨13538323523898542015279297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025549015932361343519531 13538323523898542015279297)
                ·
                  refine ⟨10153742642923906511459473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13538323523898542015279297 10153742642923906511459473)
                  ·
                    refine ⟨7615306982192929883594605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10153742642923906511459473 7615306982192929883594605)
                    ·
                      refine ⟨2855740118322348706347977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615306982192929883594605 2855740118322348706347977)
                      ·
                        rfl

theorem cell23_5561534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_5561534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561534 prefixEnd_5561534 := by exact prefixLift 5561534
  have htrace : WordTrace (prefixWord ++ tailWord_5561534) baseStart_5561534 baseEnd_5561534 := by
    simpa [prefixWord, tailWord_5561534, baseEnd_5561534] using wordTrace_append hprefix tailTrace_5561534
  have hstable : (prefixWord ++ tailWord_5561534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561534).length < 2 ^ (prefixWord ++ tailWord_5561534).sum := by decide
  have hdescent : baseEnd_5561534 < baseStart_5561534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561580 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_5561580 : Nat := 118140960795 + 5561580 * 2 ^ 59
def prefixEnd_5561580 : Nat := 4983230072969 + 3 ^ 40 * 5561580 * 2
def baseEnd_5561580 : Nat := 951921246144151842124255

theorem tailTrace_5561580 : CollatzResearch.WordTrace tailWord_5561580 prefixEnd_5561580 951921246144151842124255 := by
  unfold tailWord_5561580
  simp only [CollatzResearch.WordTrace]
  refine ⟨101423743595676488544153097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135231658127568651392204129 101423743595676488544153097)
  ·
    refine ⟨76067807696757366408114823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101423743595676488544153097 76067807696757366408114823)
    ·
      refine ⟨114101711545136049612172235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76067807696757366408114823 114101711545136049612172235)
      ·
        refine ⟨171152567317704074418258353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114101711545136049612172235 171152567317704074418258353)
        ·
          refine ⟨128364425488278055813693765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171152567317704074418258353 128364425488278055813693765)
          ·
            refine ⟨24068329779052135465067581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128364425488278055813693765 24068329779052135465067581)
            ·
              refine ⟨9025623667144550799400343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24068329779052135465067581 9025623667144550799400343)
              ·
                refine ⟨13538435500716826199100515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025623667144550799400343 13538435500716826199100515)
                ·
                  refine ⟨20307653251075239298650773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13538435500716826199100515 20307653251075239298650773)
                  ·
                    refine ⟨951921246144151842124255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20307653251075239298650773 951921246144151842124255)
                    ·
                      rfl

theorem cell23_5561580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_5561580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561580 prefixEnd_5561580 := by exact prefixLift 5561580
  have htrace : WordTrace (prefixWord ++ tailWord_5561580) baseStart_5561580 baseEnd_5561580 := by
    simpa [prefixWord, tailWord_5561580, baseEnd_5561580] using wordTrace_append hprefix tailTrace_5561580
  have hstable : (prefixWord ++ tailWord_5561580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561580).length < 2 ^ (prefixWord ++ tailWord_5561580).sum := by decide
  have hdescent : baseEnd_5561580 < baseStart_5561580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561587 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 4]
def baseStart_5561587 : Nat := 118140960795 + 5561587 * 2 ^ 59
def prefixEnd_5561587 : Nat := 4983230072969 + 3 ^ 40 * 5561587 * 2
def baseEnd_5561587 : Nat := 2855767332797036998985233

theorem tailTrace_5561587 : CollatzResearch.WordTrace tailWord_5561587 prefixEnd_5561587 2855767332797036998985233 := by
  unfold tailWord_5561587
  simp only [CollatzResearch.WordTrace]
  refine ⟨202847742502327617283811015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135231828334885078189207343 202847742502327617283811015)
  ·
    refine ⟨304271613753491425925716523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202847742502327617283811015 304271613753491425925716523)
    ·
      refine ⟨456407420630237138888574785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304271613753491425925716523 456407420630237138888574785)
      ·
        refine ⟨342305565472677854166431089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456407420630237138888574785 342305565472677854166431089)
        ·
          refine ⟨256729174104508390624823317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342305565472677854166431089 256729174104508390624823317)
          ·
            refine ⟨12034180036148830810538593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256729174104508390624823317 12034180036148830810538593)
            ·
              refine ⟨9025635027111623107903945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12034180036148830810538593 9025635027111623107903945)
              ·
                refine ⟨6769226270333717330927959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9025635027111623107903945 6769226270333717330927959)
                ·
                  refine ⟨10153839405500575996391939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769226270333717330927959 10153839405500575996391939)
                  ·
                    refine ⟨15230759108250863994587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10153839405500575996391939 15230759108250863994587909)
                    ·
                      refine ⟨2855767332797036998985233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15230759108250863994587909 2855767332797036998985233)
                      ·
                        rfl

theorem cell23_5561587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_5561587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561587 prefixEnd_5561587 := by exact prefixLift 5561587
  have htrace : WordTrace (prefixWord ++ tailWord_5561587) baseStart_5561587 baseEnd_5561587 := by
    simpa [prefixWord, tailWord_5561587, baseEnd_5561587] using wordTrace_append hprefix tailTrace_5561587
  have hstable : (prefixWord ++ tailWord_5561587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561587).length < 2 ^ (prefixWord ++ tailWord_5561587).sum := by decide
  have hdescent : baseEnd_5561587 < baseStart_5561587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5561590 : Nat := 118140960795 + 5561590 * 2 ^ 59
def prefixEnd_5561590 : Nat := 4983230072969 + 3 ^ 40 * 5561590 * 2
def baseEnd_5561590 : Nat := 2855768873239000487247719

theorem tailTrace_5561590 : CollatzResearch.WordTrace tailWord_5561590 prefixEnd_5561590 2855768873239000487247719 := by
  unfold tailWord_5561590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677990745082296799760639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135231901280877832530780149 12677990745082296799760639)
  ·
    refine ⟨19016986117623445199640959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12677990745082296799760639 19016986117623445199640959)
    ·
      refine ⟨28525479176435167799461439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19016986117623445199640959 28525479176435167799461439)
      ·
        refine ⟨42788218764652751699192159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28525479176435167799461439 42788218764652751699192159)
        ·
          refine ⟨64182328146979127548788239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42788218764652751699192159 64182328146979127548788239)
          ·
            refine ⟨96273492220468691323182359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64182328146979127548788239 96273492220468691323182359)
            ·
              refine ⟨144410238330703036984773539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96273492220468691323182359 144410238330703036984773539)
              ·
                refine ⟨216615357496054555477160309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144410238330703036984773539 216615357496054555477160309)
                ·
                  refine ⟨20307689765255114575983779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216615357496054555477160309 20307689765255114575983779)
                  ·
                    refine ⟨30461534647882671863975669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20307689765255114575983779 30461534647882671863975669)
                    ·
                      refine ⟨2855768873239000487247719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30461534647882671863975669 2855768873239000487247719)
                      ·
                        rfl

theorem cell23_5561590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5561590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561590 prefixEnd_5561590 := by exact prefixLift 5561590
  have htrace : WordTrace (prefixWord ++ tailWord_5561590) baseStart_5561590 baseEnd_5561590 := by
    simpa [prefixWord, tailWord_5561590, baseEnd_5561590] using wordTrace_append hprefix tailTrace_5561590
  have hstable : (prefixWord ++ tailWord_5561590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561590).length < 2 ^ (prefixWord ++ tailWord_5561590).sum := by decide
  have hdescent : baseEnd_5561590 < baseStart_5561590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561593 : List Nat := [1, 2, 1, 3, 1, 1, 5, 9]
def baseStart_5561593 : Nat := 118140960795 + 5561593 * 2 ^ 59
def prefixEnd_5561593 : Nat := 4983230072969 + 3 ^ 40 * 5561593 * 2
def baseEnd_5561593 : Nat := 105769274580776443537415

theorem tailTrace_5561593 : CollatzResearch.WordTrace tailWord_5561593 prefixEnd_5561593 105769274580776443537415 := by
  unfold tailWord_5561593
  simp only [CollatzResearch.WordTrace]
  refine ⟨202847961340305880308529433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135231974226870586872352955 202847961340305880308529433)
  ·
    refine ⟨152135971005229410231397075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202847961340305880308529433 152135971005229410231397075)
    ·
      refine ⟨228203956507844115347095613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152135971005229410231397075 228203956507844115347095613)
      ·
        refine ⟨85576483690441543255160855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228203956507844115347095613 85576483690441543255160855)
        ·
          refine ⟨128364725535662314882741283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85576483690441543255160855 128364725535662314882741283)
          ·
            refine ⟨192547088303493472324111925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128364725535662314882741283 192547088303493472324111925)
            ·
              refine ⟨18051289528452513030385493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192547088303493472324111925 18051289528452513030385493)
              ·
                refine ⟨105769274580776443537415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18051289528452513030385493 105769274580776443537415)
                ·
                  rfl

theorem cell23_5561593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 9].length) (baseStart_5561593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561593 prefixEnd_5561593 := by exact prefixLift 5561593
  have htrace : WordTrace (prefixWord ++ tailWord_5561593) baseStart_5561593 baseEnd_5561593 := by
    simpa [prefixWord, tailWord_5561593, baseEnd_5561593] using wordTrace_append hprefix tailTrace_5561593
  have hstable : (prefixWord ++ tailWord_5561593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561593).length < 2 ^ (prefixWord ++ tailWord_5561593).sum := by decide
  have hdescent : baseEnd_5561593 < baseStart_5561593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561598 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5561598 : Nat := 118140960795 + 5561598 * 2 ^ 59
def prefixEnd_5561598 : Nat := 4983230072969 + 3 ^ 40 * 5561598 * 2
def baseEnd_5561598 : Nat := 2855772981084236455947683

theorem tailTrace_5561598 : CollatzResearch.WordTrace tailWord_5561598 prefixEnd_5561598 2855772981084236455947683 := by
  unfold tailWord_5561598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356017963160970770307681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135232095803525177441640965 25356017963160970770307681)
  ·
    refine ⟨19017013472370728077730761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25356017963160970770307681 19017013472370728077730761)
    ·
      refine ⟨14262760104278046058298071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19017013472370728077730761 14262760104278046058298071)
      ·
        refine ⟨21394140156417069087447107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262760104278046058298071 21394140156417069087447107)
        ·
          refine ⟨32091210234625603631170661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21394140156417069087447107 32091210234625603631170661)
          ·
            refine ⟨6017101918992300680844499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32091210234625603631170661 6017101918992300680844499)
            ·
              refine ⟨9025652878488451021266749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017101918992300680844499 9025652878488451021266749)
              ·
                refine ⟨3384619829433169132975031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9025652878488451021266749 3384619829433169132975031)
                ·
                  refine ⟨5076929744149753699462547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384619829433169132975031 5076929744149753699462547)
                  ·
                    refine ⟨7615394616224630549193821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5076929744149753699462547 7615394616224630549193821)
                    ·
                      refine ⟨2855772981084236455947683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615394616224630549193821 2855772981084236455947683)
                      ·
                        rfl

theorem cell23_5561598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5561598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561598 prefixEnd_5561598 := by exact prefixLift 5561598
  have htrace : WordTrace (prefixWord ++ tailWord_5561598) baseStart_5561598 baseEnd_5561598 := by
    simpa [prefixWord, tailWord_5561598, baseEnd_5561598] using wordTrace_append hprefix tailTrace_5561598
  have hstable : (prefixWord ++ tailWord_5561598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561598).length < 2 ^ (prefixWord ++ tailWord_5561598).sum := by decide
  have hdescent : baseEnd_5561598 < baseStart_5561598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561631 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 2, 4]
def baseStart_5561631 : Nat := 118140960795 + 5561631 * 2 ^ 59
def prefixEnd_5561631 : Nat := 4983230072969 + 3 ^ 40 * 5561631 * 2
def baseEnd_5561631 : Nat := 951929975315278275611677

theorem tailTrace_5561631 : CollatzResearch.WordTrace tailWord_5561631 prefixEnd_5561631 951929975315278275611677 := by
  unfold tailWord_5561631
  simp only [CollatzResearch.WordTrace]
  refine ⟨202849347314168212798412747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135232898209445475198941831 202849347314168212798412747)
  ·
    refine ⟨304274020971252319197619121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202849347314168212798412747 304274020971252319197619121)
    ·
      refine ⟨228205515728439239398214341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304274020971252319197619121 228205515728439239398214341)
      ·
        refine ⟨42788534199082357387165189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228205515728439239398214341 42788534199082357387165189)
        ·
          refine ⟨8022850162327942010093473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42788534199082357387165189 8022850162327942010093473)
          ·
            refine ⟨6017137621745956507570105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022850162327942010093473 6017137621745956507570105)
            ·
              refine ⟨4512853216309467380677579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017137621745956507570105 4512853216309467380677579)
              ·
                refine ⟨6769279824464201071016369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512853216309467380677579 6769279824464201071016369)
                ·
                  refine ⟨5076959868348150803262277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6769279824464201071016369 5076959868348150803262277)
                  ·
                    refine ⟨951929975315278275611677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076959868348150803262277 951929975315278275611677)
                    ·
                      rfl

theorem cell23_5561631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_5561631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561631 prefixEnd_5561631 := by exact prefixLift 5561631
  have htrace : WordTrace (prefixWord ++ tailWord_5561631) baseStart_5561631 baseEnd_5561631 := by
    simpa [prefixWord, tailWord_5561631, baseEnd_5561631] using wordTrace_append hprefix tailTrace_5561631
  have hstable : (prefixWord ++ tailWord_5561631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561631).length < 2 ^ (prefixWord ++ tailWord_5561631).sum := by decide
  have hdescent : baseEnd_5561631 < baseStart_5561631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561680 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_5561680 : Nat := 118140960795 + 5561680 * 2 ^ 59
def prefixEnd_5561680 : Nat := 4983230072969 + 3 ^ 40 * 5561680 * 2
def baseEnd_5561680 : Nat := 2855815086497905135122305

theorem tailTrace_5561680 : CollatzResearch.WordTrace tailWord_5561680 prefixEnd_5561680 2855815086497905135122305 := by
  unfold tailWord_5561680
  simp only [CollatzResearch.WordTrace]
  refine ⟨101425567245495347083473247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135234089660660462777964329 101425567245495347083473247)
  ·
    refine ⟨152138350868243020625209871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101425567245495347083473247 152138350868243020625209871)
    ·
      refine ⟨228207526302364530937814807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152138350868243020625209871 228207526302364530937814807)
      ·
        refine ⟨342311289453546796406722211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228207526302364530937814807 342311289453546796406722211)
        ·
          refine ⟨513466934180320194610083317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342311289453546796406722211 513466934180320194610083317)
          ·
            refine ⟨48137525079405018244695311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 513466934180320194610083317 48137525079405018244695311)
            ·
              refine ⟨72206287619107527367042967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48137525079405018244695311 72206287619107527367042967)
              ·
                refine ⟨108309431428661291050564451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72206287619107527367042967 108309431428661291050564451)
                ·
                  refine ⟨162464147142991936575846677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108309431428661291050564451 162464147142991936575846677)
                  ·
                    refine ⟨7615506897327747026992813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 162464147142991936575846677 7615506897327747026992813)
                    ·
                      refine ⟨2855815086497905135122305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615506897327747026992813 2855815086497905135122305)
                      ·
                        rfl

theorem cell23_5561680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_5561680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561680 prefixEnd_5561680 := by exact prefixLift 5561680
  have htrace : WordTrace (prefixWord ++ tailWord_5561680) baseStart_5561680 baseEnd_5561680 := by
    simpa [prefixWord, tailWord_5561680, baseEnd_5561680] using wordTrace_append hprefix tailTrace_5561680
  have hstable : (prefixWord ++ tailWord_5561680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561680).length < 2 ^ (prefixWord ++ tailWord_5561680).sum := by decide
  have hdescent : baseEnd_5561680 < baseStart_5561680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561690 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5561690 : Nat := 118140960795 + 5561690 * 2 ^ 59
def prefixEnd_5561690 : Nat := 4983230072969 + 3 ^ 40 * 5561690 * 2
def baseEnd_5561690 : Nat := 2855820221304450095997259

theorem tailTrace_5561690 : CollatzResearch.WordTrace tailWord_5561690 prefixEnd_5561690 2855820221304450095997259 := by
  unfold tailWord_5561690
  simp only [CollatzResearch.WordTrace]
  refine ⟨50712874805238616468702631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135234332813969643916540349 50712874805238616468702631)
  ·
    refine ⟨76069312207857924703053947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50712874805238616468702631 76069312207857924703053947)
    ·
      refine ⟨114103968311786887054580921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76069312207857924703053947 114103968311786887054580921)
      ·
        refine ⟨85577976233840165290935691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114103968311786887054580921 85577976233840165290935691)
        ·
          refine ⟨128366964350760247936403537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85577976233840165290935691 128366964350760247936403537)
          ·
            refine ⟨96275223263070185952302653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128366964350760247936403537 96275223263070185952302653)
            ·
              refine ⟨36103208723651319732113495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96275223263070185952302653 36103208723651319732113495)
              ·
                refine ⟨54154813085476979598170243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36103208723651319732113495 54154813085476979598170243)
                ·
                  refine ⟨81232219628215469397255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54154813085476979598170243 81232219628215469397255365)
                  ·
                    refine ⟨15231041180290400511985381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81232219628215469397255365 15231041180290400511985381)
                    ·
                      refine ⟨2855820221304450095997259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15231041180290400511985381 2855820221304450095997259)
                      ·
                        rfl

theorem cell23_5561690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5561690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561690 prefixEnd_5561690 := by exact prefixLift 5561690
  have htrace : WordTrace (prefixWord ++ tailWord_5561690) baseStart_5561690 baseEnd_5561690 := by
    simpa [prefixWord, tailWord_5561690, baseEnd_5561690] using wordTrace_append hprefix tailTrace_5561690
  have hstable : (prefixWord ++ tailWord_5561690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561690).length < 2 ^ (prefixWord ++ tailWord_5561690).sum := by decide
  have hdescent : baseEnd_5561690 < baseStart_5561690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561700 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 9]
def baseStart_5561700 : Nat := 118140960795 + 5561700 * 2 ^ 59
def prefixEnd_5561700 : Nat := 4983230072969 + 3 ^ 40 * 5561700 * 2
def baseEnd_5561700 : Nat := 317313928456777228541357

theorem tailTrace_5561700 : CollatzResearch.WordTrace tailWord_5561700 prefixEnd_5561700 317313928456777228541357 := by
  unfold tailWord_5561700
  simp only [CollatzResearch.WordTrace]
  refine ⟨101425931975459118791337277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135234575967278825055116369 101425931975459118791337277)
  ·
    refine ⟨38034724490797169546751479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101425931975459118791337277 38034724490797169546751479)
    ·
      refine ⟨57052086736195754320127219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38034724490797169546751479 57052086736195754320127219)
      ·
        refine ⟨85578130104293631480190829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57052086736195754320127219 85578130104293631480190829)
        ·
          refine ⟨32091798789110111805071561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85578130104293631480190829 32091798789110111805071561)
          ·
            refine ⟨24068849091832583853803671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32091798789110111805071561 24068849091832583853803671)
            ·
              refine ⟨36103273637748875780705507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24068849091832583853803671 36103273637748875780705507)
              ·
                refine ⟨54154910456623313671058261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36103273637748875780705507 54154910456623313671058261)
                ·
                  refine ⟨317313928456777228541357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54154910456623313671058261 317313928456777228541357)
                  ·
                    rfl

theorem cell23_5561700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_5561700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561700 prefixEnd_5561700 := by exact prefixLift 5561700
  have htrace : WordTrace (prefixWord ++ tailWord_5561700) baseStart_5561700 baseEnd_5561700 := by
    simpa [prefixWord, tailWord_5561700, baseEnd_5561700] using wordTrace_append hprefix tailTrace_5561700
  have hstable : (prefixWord ++ tailWord_5561700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561700).length < 2 ^ (prefixWord ++ tailWord_5561700).sum := by decide
  have hdescent : baseEnd_5561700 < baseStart_5561700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561740 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5561740 : Nat := 118140960795 + 5561740 * 2 ^ 59
def prefixEnd_5561740 : Nat := 4983230072969 + 3 ^ 40 * 5561740 * 2
def baseEnd_5561740 : Nat := 2855845895337174900372029

theorem tailTrace_5561740 : CollatzResearch.WordTrace tailWord_5561740 prefixEnd_5561740 2855845895337174900372029 := by
  unfold tailWord_5561740
  simp only [CollatzResearch.WordTrace]
  refine ⟨101426661435386662207065337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135235548580515549609420449 101426661435386662207065337)
  ·
    refine ⟨76069996076539996655299003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101426661435386662207065337 76069996076539996655299003)
    ·
      refine ⟨114104994114809994982948505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76069996076539996655299003 114104994114809994982948505)
      ·
        refine ⟨85578745586107496237211379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114104994114809994982948505 85578745586107496237211379)
        ·
          refine ⟨128368118379161244355817069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85578745586107496237211379 128368118379161244355817069)
          ·
            refine ⟨48138044392185466633431401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128368118379161244355817069 48138044392185466633431401)
            ·
              refine ⟨36103533294139099975073551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48138044392185466633431401 36103533294139099975073551)
              ·
                refine ⟨54155299941208649962610327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36103533294139099975073551 54155299941208649962610327)
                ·
                  refine ⟨81232949911812974943915491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54155299941208649962610327 81232949911812974943915491)
                  ·
                    refine ⟨121849424867719462415873237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81232949911812974943915491 121849424867719462415873237)
                    ·
                      refine ⟨2855845895337174900372029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121849424867719462415873237 2855845895337174900372029)
                      ·
                        rfl

theorem cell23_5561740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5561740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561740 prefixEnd_5561740 := by exact prefixLift 5561740
  have htrace : WordTrace (prefixWord ++ tailWord_5561740) baseStart_5561740 baseEnd_5561740 := by
    simpa [prefixWord, tailWord_5561740, baseEnd_5561740] using wordTrace_append hprefix tailTrace_5561740
  have hstable : (prefixWord ++ tailWord_5561740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561740).length < 2 ^ (prefixWord ++ tailWord_5561740).sum := by decide
  have hdescent : baseEnd_5561740 < baseStart_5561740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561760 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_5561760 : Nat := 118140960795 + 5561760 * 2 ^ 59
def prefixEnd_5561760 : Nat := 4983230072969 + 3 ^ 40 * 5561760 * 2
def baseEnd_5561760 : Nat := 951952054983421607373979

theorem tailTrace_5561760 : CollatzResearch.WordTrace tailWord_5561760 prefixEnd_5561760 951952054983421607373979 := by
  unfold tailWord_5561760
  simp only [CollatzResearch.WordTrace]
  refine ⟨101427026165350433914929367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135236034887133911886572489 101427026165350433914929367)
  ·
    refine ⟨152140539248025650872394051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101427026165350433914929367 152140539248025650872394051)
    ·
      refine ⟨228210808872038476308591077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152140539248025650872394051 228210808872038476308591077)
      ·
        refine ⟨42789526663507214307860827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228210808872038476308591077 42789526663507214307860827)
        ·
          refine ⟨64184289995260821461791241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42789526663507214307860827 64184289995260821461791241)
          ·
            refine ⟨48138217496445616096343431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64184289995260821461791241 48138217496445616096343431)
            ·
              refine ⟨72207326244668424144515147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48138217496445616096343431 72207326244668424144515147)
              ·
                refine ⟨108310989367002636216772721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72207326244668424144515147 108310989367002636216772721)
                ·
                  refine ⟨81233242025251977162579541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108310989367002636216772721 81233242025251977162579541)
                  ·
                    refine ⟨951952054983421607373979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81233242025251977162579541 951952054983421607373979)
                    ·
                      rfl

theorem cell23_5561760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_5561760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561760 prefixEnd_5561760 := by exact prefixLift 5561760
  have htrace : WordTrace (prefixWord ++ tailWord_5561760) baseStart_5561760 baseEnd_5561760 := by
    simpa [prefixWord, tailWord_5561760, baseEnd_5561760] using wordTrace_append hprefix tailTrace_5561760
  have hstable : (prefixWord ++ tailWord_5561760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561760).length < 2 ^ (prefixWord ++ tailWord_5561760).sum := by decide
  have hdescent : baseEnd_5561760 < baseStart_5561760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561767 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5561767 : Nat := 118140960795 + 5561767 * 2 ^ 59
def prefixEnd_5561767 : Nat := 4983230072969 + 3 ^ 40 * 5561767 * 2
def baseEnd_5561767 : Nat := 2855859759314846294734405

theorem tailTrace_5561767 : CollatzResearch.WordTrace tailWord_5561767 prefixEnd_5561767 2855859759314846294734405 := by
  unfold tailWord_5561767
  simp only [CollatzResearch.WordTrace]
  refine ⟨202854307641675508025363555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135236205094450338683575703 202854307641675508025363555)
  ·
    refine ⟨304281461462513262038045333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202854307641675508025363555 304281461462513262038045333)
    ·
      refine ⟨14263193506055309158033375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304281461462513262038045333 14263193506055309158033375)
      ·
        refine ⟨21394790259082963737050063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14263193506055309158033375 21394790259082963737050063)
        ·
          refine ⟨32092185388624445605575095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21394790259082963737050063 32092185388624445605575095)
          ·
            refine ⟨48138278082936668408362643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32092185388624445605575095 48138278082936668408362643)
            ·
              refine ⟨72207417124405002612543965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48138278082936668408362643 72207417124405002612543965)
              ·
                refine ⟨27077781421651875979703987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72207417124405002612543965 27077781421651875979703987)
                ·
                  refine ⟨40616672132477813969555981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27077781421651875979703987 40616672132477813969555981)
                  ·
                    refine ⟨15231252049679180238583493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40616672132477813969555981 15231252049679180238583493)
                    ·
                      refine ⟨2855859759314846294734405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15231252049679180238583493 2855859759314846294734405)
                      ·
                        rfl

theorem cell23_5561767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5561767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561767 prefixEnd_5561767 := by exact prefixLift 5561767
  have htrace : WordTrace (prefixWord ++ tailWord_5561767) baseStart_5561767 baseEnd_5561767 := by
    simpa [prefixWord, tailWord_5561767, baseEnd_5561767] using wordTrace_append hprefix tailTrace_5561767
  have hstable : (prefixWord ++ tailWord_5561767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561767).length < 2 ^ (prefixWord ++ tailWord_5561767).sum := by decide
  have hdescent : baseEnd_5561767 < baseStart_5561767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561768 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 5]
def baseStart_5561768 : Nat := 118140960795 + 5561768 * 2 ^ 59
def prefixEnd_5561768 : Nat := 4983230072969 + 3 ^ 40 * 5561768 * 2
def baseEnd_5561768 : Nat := 317317808088388976757989

theorem tailTrace_5561768 : CollatzResearch.WordTrace tailWord_5561768 prefixEnd_5561768 317317808088388976757989 := by
  unfold tailWord_5561768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101427172057335942598074979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135236229409781256797433305 101427172057335942598074979)
  ·
    refine ⟨152140758086003913897112469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101427172057335942598074979 152140758086003913897112469)
    ·
      refine ⟨7131598035281433463927147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152140758086003913897112469 7131598035281433463927147)
      ·
        refine ⟨10697397052922150195890721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131598035281433463927147 10697397052922150195890721)
        ·
          refine ⟨8023047789691612646918041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10697397052922150195890721 8023047789691612646918041)
          ·
            refine ⟨6017285842268709485188531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8023047789691612646918041 6017285842268709485188531)
            ·
              refine ⟨9025928763403064227782797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017285842268709485188531 9025928763403064227782797)
              ·
                refine ⟨3384723286276149085418549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9025928763403064227782797 3384723286276149085418549)
                ·
                  refine ⟨317317808088388976757989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384723286276149085418549 317317808088388976757989)
                  ·
                    rfl

theorem cell23_5561768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 5].length) (baseStart_5561768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561768 prefixEnd_5561768 := by exact prefixLift 5561768
  have htrace : WordTrace (prefixWord ++ tailWord_5561768) baseStart_5561768 baseEnd_5561768 := by
    simpa [prefixWord, tailWord_5561768, baseEnd_5561768] using wordTrace_append hprefix tailTrace_5561768
  have hstable : (prefixWord ++ tailWord_5561768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561768).length < 2 ^ (prefixWord ++ tailWord_5561768).sum := by decide
  have hdescent : baseEnd_5561768 < baseStart_5561768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561821 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5561821 : Nat := 118140960795 + 5561821 * 2 ^ 59
def prefixEnd_5561821 : Nat := 4983230072969 + 3 ^ 40 * 5561821 * 2
def baseEnd_5561821 : Nat := 2855887487270189083459157

theorem tailTrace_5561821 : CollatzResearch.WordTrace tailWord_5561821 prefixEnd_5561821 2855887487270189083459157 := by
  unfold tailWord_5561821
  simp only [CollatzResearch.WordTrace]
  refine ⟨202856277183479875247829317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135237518122319916831886211 202856277183479875247829317)
  ·
    refine ⟨38035551971902476608967997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202856277183479875247829317 38035551971902476608967997)
    ·
      refine ⟨14263331989463428728362999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38035551971902476608967997 14263331989463428728362999)
      ·
        refine ⟨21394997984195143092544499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14263331989463428728362999 21394997984195143092544499)
        ·
          refine ⟨32092496976292714638816749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21394997984195143092544499 32092496976292714638816749)
          ·
            refine ⟨12034686366109767989556281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32092496976292714638816749 12034686366109767989556281)
            ·
              refine ⟨9026014774582325992167211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12034686366109767989556281 9026014774582325992167211)
              ·
                refine ⟨13539022161873488988250817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9026014774582325992167211 13539022161873488988250817)
                ·
                  refine ⟨10154266621405116741188113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13539022161873488988250817 10154266621405116741188113)
                  ·
                    refine ⟨7615699966053837555891085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10154266621405116741188113 7615699966053837555891085)
                    ·
                      refine ⟨2855887487270189083459157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615699966053837555891085 2855887487270189083459157)
                      ·
                        rfl

theorem cell23_5561821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5561821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561821 prefixEnd_5561821 := by exact prefixLift 5561821
  have htrace : WordTrace (prefixWord ++ tailWord_5561821) baseStart_5561821 baseEnd_5561821 := by
    simpa [prefixWord, tailWord_5561821, baseEnd_5561821] using wordTrace_append hprefix tailTrace_5561821
  have hstable : (prefixWord ++ tailWord_5561821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561821).length < 2 ^ (prefixWord ++ tailWord_5561821).sum := by decide
  have hdescent : baseEnd_5561821 < baseStart_5561821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561845 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5561845 : Nat := 118140960795 + 5561845 * 2 ^ 59
def prefixEnd_5561845 : Nat := 4983230072969 + 3 ^ 40 * 5561845 * 2
def baseEnd_5561845 : Nat := 951966603601965663186349

theorem tailTrace_5561845 : CollatzResearch.WordTrace tailWord_5561845 prefixEnd_5561845 951966603601965663186349 := by
  unfold tailWord_5561845
  simp only [CollatzResearch.WordTrace]
  refine ⟨202857152535392927346702989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135238101690261951564468659 202857152535392927346702989)
  ·
    refine ⟨76071432200772347755013621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202857152535392927346702989 76071432200772347755013621)
    ·
      refine ⟨7131696768822407602032527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76071432200772347755013621 7131696768822407602032527)
      ·
        refine ⟨10697545153233611403048791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131696768822407602032527 10697545153233611403048791)
        ·
          refine ⟨16046317729850417104573187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697545153233611403048791 16046317729850417104573187)
          ·
            refine ⟨24069476594775625656859781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16046317729850417104573187 24069476594775625656859781)
            ·
              refine ⟨4513026861520429810661209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24069476594775625656859781 4513026861520429810661209)
              ·
                refine ⟨3384770146140322357995907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513026861520429810661209 3384770146140322357995907)
                ·
                  refine ⟨5077155219210483536993861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384770146140322357995907 5077155219210483536993861)
                  ·
                    refine ⟨951966603601965663186349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077155219210483536993861 951966603601965663186349)
                    ·
                      rfl

theorem cell23_5561845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5561845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561845 prefixEnd_5561845 := by exact prefixLift 5561845
  have htrace : WordTrace (prefixWord ++ tailWord_5561845) baseStart_5561845 baseEnd_5561845 := by
    simpa [prefixWord, tailWord_5561845, baseEnd_5561845] using wordTrace_append hprefix tailTrace_5561845
  have hstable : (prefixWord ++ tailWord_5561845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561845).length < 2 ^ (prefixWord ++ tailWord_5561845).sum := by decide
  have hdescent : baseEnd_5561845 < baseStart_5561845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 1, 1, 3]
def baseStart_5561851 : Nat := 118140960795 + 5561851 * 2 ^ 59
def prefixEnd_5561851 : Nat := 4983230072969 + 3 ^ 40 * 5561851 * 2
def baseEnd_5561851 : Nat := 2855902891689823966084019

theorem tailTrace_5561851 : CollatzResearch.WordTrace tailWord_5561851 prefixEnd_5561851 2855902891689823966084019 := by
  unfold tailWord_5561851
  simp only [CollatzResearch.WordTrace]
  refine ⟨202857371373371190371421407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135238247582247460247614271 202857371373371190371421407)
  ·
    refine ⟨304286057060056785557132111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202857371373371190371421407 304286057060056785557132111)
    ·
      refine ⟨456429085590085178335698167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304286057060056785557132111 456429085590085178335698167)
      ·
        refine ⟨684643628385127767503547251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456429085590085178335698167 684643628385127767503547251)
        ·
          refine ⟨1026965442577691651255320877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684643628385127767503547251 1026965442577691651255320877)
          ·
            refine ⟨385112040966634369220745329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1026965442577691651255320877 385112040966634369220745329)
            ·
              refine ⟨288834030724975776915558997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385112040966634369220745329 288834030724975776915558997)
              ·
                refine ⟨3384773797558309885729207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 288834030724975776915558997 3384773797558309885729207)
                ·
                  refine ⟨5077160696337464828593811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384773797558309885729207 5077160696337464828593811)
                  ·
                    refine ⟨7615741044506197242890717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077160696337464828593811 7615741044506197242890717)
                    ·
                      refine ⟨2855902891689823966084019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7615741044506197242890717 2855902891689823966084019)
                      ·
                        rfl

theorem cell23_5561851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 1, 3].length) (baseStart_5561851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561851 prefixEnd_5561851 := by exact prefixLift 5561851
  have htrace : WordTrace (prefixWord ++ tailWord_5561851) baseStart_5561851 baseEnd_5561851 := by
    simpa [prefixWord, tailWord_5561851, baseEnd_5561851] using wordTrace_append hprefix tailTrace_5561851
  have hstable : (prefixWord ++ tailWord_5561851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561851).length < 2 ^ (prefixWord ++ tailWord_5561851).sum := by decide
  have hdescent : baseEnd_5561851 < baseStart_5561851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561884 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_5561884 : Nat := 118140960795 + 5561884 * 2 ^ 59
def prefixEnd_5561884 : Nat := 4983230072969 + 3 ^ 40 * 5561884 * 2
def baseEnd_5561884 : Nat := 951973278850474112323789

theorem tailTrace_5561884 : CollatzResearch.WordTrace tailWord_5561884 prefixEnd_5561884 951973278850474112323789 := by
  unfold tailWord_5561884
  simp only [CollatzResearch.WordTrace]
  refine ⟨101429287491125818503686353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135239049988167758004915137 101429287491125818503686353)
  ·
    refine ⟨76071965618344363877764765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101429287491125818503686353 76071965618344363877764765)
    ·
      refine ⟨28526987106879136454161787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76071965618344363877764765 28526987106879136454161787)
      ·
        refine ⟨42790480660318704681242681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28526987106879136454161787 42790480660318704681242681)
        ·
          refine ⟨32092860495239028510932011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42790480660318704681242681 32092860495239028510932011)
          ·
            refine ⟨48139290742858542766398017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32092860495239028510932011 48139290742858542766398017)
            ·
              refine ⟨36104468057143907074798513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48139290742858542766398017 36104468057143907074798513)
              ·
                refine ⟨27078351042857930306098885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36104468057143907074798513 27078351042857930306098885)
                ·
                  refine ⟨5077190820535861932393541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27078351042857930306098885 5077190820535861932393541)
                  ·
                    refine ⟨951973278850474112323789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077190820535861932393541 951973278850474112323789)
                    ·
                      rfl

theorem cell23_5561884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_5561884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561884 prefixEnd_5561884 := by exact prefixLift 5561884
  have htrace : WordTrace (prefixWord ++ tailWord_5561884) baseStart_5561884 baseEnd_5561884 := by
    simpa [prefixWord, tailWord_5561884, baseEnd_5561884] using wordTrace_append hprefix tailTrace_5561884
  have hstable : (prefixWord ++ tailWord_5561884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561884).length < 2 ^ (prefixWord ++ tailWord_5561884).sum := by decide
  have hdescent : baseEnd_5561884 < baseStart_5561884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561888 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_5561888 : Nat := 118140960795 + 5561888 * 2 ^ 59
def prefixEnd_5561888 : Nat := 4983230072969 + 3 ^ 40 * 5561888 * 2
def baseEnd_5561888 : Nat := 951973963491346773773783

theorem tailTrace_5561888 : CollatzResearch.WordTrace tailWord_5561888 prefixEnd_5561888 951973963491346773773783 := by
  unfold tailWord_5561888
  simp only [CollatzResearch.WordTrace]
  refine ⟨101429360437118572845259159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135239147249491430460345545 101429360437118572845259159)
  ·
    refine ⟨152144040655677859267888739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101429360437118572845259159 152144040655677859267888739)
    ·
      refine ⟨228216060983516788901833109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152144040655677859267888739 228216060983516788901833109)
      ·
        refine ⟨10697627858602349479773427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228216060983516788901833109 10697627858602349479773427)
        ·
          refine ⟨16046441787903524219660141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697627858602349479773427 16046441787903524219660141)
          ·
            refine ⟨6017415670463821582372553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16046441787903524219660141 6017415670463821582372553)
            ·
              refine ⟨4513061752847866186779415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017415670463821582372553 4513061752847866186779415)
              ·
                refine ⟨6769592629271799280169123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513061752847866186779415 6769592629271799280169123)
                ·
                  refine ⟨10154388943907698920253685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769592629271799280169123 10154388943907698920253685)
                  ·
                    refine ⟨951973963491346773773783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10154388943907698920253685 951973963491346773773783)
                    ·
                      rfl

theorem cell23_5561888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_5561888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561888 prefixEnd_5561888 := by exact prefixLift 5561888
  have htrace : WordTrace (prefixWord ++ tailWord_5561888) baseStart_5561888 baseEnd_5561888 := by
    simpa [prefixWord, tailWord_5561888, baseEnd_5561888] using wordTrace_append hprefix tailTrace_5561888
  have hstable : (prefixWord ++ tailWord_5561888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561888).length < 2 ^ (prefixWord ++ tailWord_5561888).sum := by decide
  have hdescent : baseEnd_5561888 < baseStart_5561888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561891 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 4]
def baseStart_5561891 : Nat := 118140960795 + 5561891 * 2 ^ 59
def prefixEnd_5561891 : Nat := 4983230072969 + 3 ^ 40 * 5561891 * 2
def baseEnd_5561891 : Nat := 2855923430916003809583835

theorem tailTrace_5561891 : CollatzResearch.WordTrace tailWord_5561891 prefixEnd_5561891 2855923430916003809583835 := by
  unfold tailWord_5561891
  simp only [CollatzResearch.WordTrace]
  refine ⟨202858830293226277202877527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135239220195484184801918351 202858830293226277202877527)
  ·
    refine ⟨304288245439839415804316291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202858830293226277202877527 304288245439839415804316291)
    ·
      refine ⟨456432368159759123706474437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304288245439839415804316291 456432368159759123706474437)
      ·
        refine ⟨85581069029954835694963957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 456432368159759123706474437 85581069029954835694963957)
        ·
          refine ⟨8023225221558265846402871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85581069029954835694963957 8023225221558265846402871)
          ·
            refine ⟨12034837832337398769604307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023225221558265846402871 12034837832337398769604307)
            ·
              refine ⟨18052256748506098154406461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034837832337398769604307 18052256748506098154406461)
              ·
                refine ⟨6769596280689786807902423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18052256748506098154406461 6769596280689786807902423)
                ·
                  refine ⟨10154394421034680211853635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769596280689786807902423 10154394421034680211853635)
                  ·
                    refine ⟨15231591631552020317780453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10154394421034680211853635 15231591631552020317780453)
                    ·
                      refine ⟨2855923430916003809583835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15231591631552020317780453 2855923430916003809583835)
                      ·
                        rfl

theorem cell23_5561891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_5561891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561891 prefixEnd_5561891 := by exact prefixLift 5561891
  have htrace : WordTrace (prefixWord ++ tailWord_5561891) baseStart_5561891 baseEnd_5561891 := by
    simpa [prefixWord, tailWord_5561891, baseEnd_5561891] using wordTrace_append hprefix tailTrace_5561891
  have hstable : (prefixWord ++ tailWord_5561891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561891).length < 2 ^ (prefixWord ++ tailWord_5561891).sum := by decide
  have hdescent : baseEnd_5561891 < baseStart_5561891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561937 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_5561937 : Nat := 118140960795 + 5561937 * 2 ^ 59
def prefixEnd_5561937 : Nat := 4983230072969 + 3 ^ 40 * 5561937 * 2
def baseEnd_5561937 : Nat := 2855947051026110629608623

theorem tailTrace_5561937 : CollatzResearch.WordTrace tailWord_5561937 prefixEnd_5561937 2855947051026110629608623 := by
  unfold tailWord_5561937
  simp only [CollatzResearch.WordTrace]
  refine ⟨202860508051059627059052065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135240338700706418039368043 202860508051059627059052065)
  ·
    refine ⟨152145381038294720294289049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202860508051059627059052065 152145381038294720294289049)
    ·
      refine ⟨114109035778721040220716787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152145381038294720294289049 114109035778721040220716787)
      ·
        refine ⟨171163553668081560331075181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114109035778721040220716787 171163553668081560331075181)
        ·
          refine ⟨64186332625530585124153193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171163553668081560331075181 64186332625530585124153193)
          ·
            refine ⟨48139749469147938843114895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64186332625530585124153193 48139749469147938843114895)
            ·
              refine ⟨72209624203721908264672343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48139749469147938843114895 72209624203721908264672343)
              ·
                refine ⟨108314436305582862397008515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72209624203721908264672343 108314436305582862397008515)
                ·
                  refine ⟨162471654458374293595512773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108314436305582862397008515 162471654458374293595512773)
                  ·
                    refine ⟨30463435210945180049158645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162471654458374293595512773 30463435210945180049158645)
                    ·
                      refine ⟨2855947051026110629608623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30463435210945180049158645 2855947051026110629608623)
                      ·
                        rfl

theorem cell23_5561937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_5561937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561937 prefixEnd_5561937 := by exact prefixLift 5561937
  have htrace : WordTrace (prefixWord ++ tailWord_5561937) baseStart_5561937 baseEnd_5561937 := by
    simpa [prefixWord, tailWord_5561937, baseEnd_5561937] using wordTrace_append hprefix tailTrace_5561937
  have hstable : (prefixWord ++ tailWord_5561937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561937).length < 2 ^ (prefixWord ++ tailWord_5561937).sum := by decide
  have hdescent : baseEnd_5561937 < baseStart_5561937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561967 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_5561967 : Nat := 118140960795 + 5561967 * 2 ^ 59
def prefixEnd_5561967 : Nat := 4983230072969 + 3 ^ 40 * 5561967 * 2
def baseEnd_5561967 : Nat := 2855962455445745512233485

theorem tailTrace_5561967 : CollatzResearch.WordTrace tailWord_5561967 prefixEnd_5561967 2855962455445745512233485 := by
  unfold tailWord_5561967
  simp only [CollatzResearch.WordTrace]
  refine ⟨202861602240950942182644155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135241068160633961455096103 202861602240950942182644155)
  ·
    refine ⟨304292403361426413273966233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202861602240950942182644155 304292403361426413273966233)
    ·
      refine ⟨228219302521069809955474675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304292403361426413273966233 228219302521069809955474675)
      ·
        refine ⟨342328953781604714933212013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228219302521069809955474675 342328953781604714933212013)
        ·
          refine ⟨128373357668101768099954505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342328953781604714933212013 128373357668101768099954505)
          ·
            refine ⟨96280018251076326074965879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128373357668101768099954505 96280018251076326074965879)
            ·
              refine ⟨144420027376614489112448819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96280018251076326074965879 144420027376614489112448819)
              ·
                refine ⟨216630041064921733668673229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144420027376614489112448819 216630041064921733668673229)
                ·
                  refine ⟨81236265399345650125752461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216630041064921733668673229 81236265399345650125752461)
                  ·
                    refine ⟨30463599524754618797157173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81236265399345650125752461 30463599524754618797157173)
                    ·
                      refine ⟨2855962455445745512233485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30463599524754618797157173 2855962455445745512233485)
                      ·
                        rfl

theorem cell23_5561967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_5561967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561967 prefixEnd_5561967 := by exact prefixLift 5561967
  have htrace : WordTrace (prefixWord ++ tailWord_5561967) baseStart_5561967 baseEnd_5561967 := by
    simpa [prefixWord, tailWord_5561967, baseEnd_5561967] using wordTrace_append hprefix tailTrace_5561967
  have hstable : (prefixWord ++ tailWord_5561967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561967).length < 2 ^ (prefixWord ++ tailWord_5561967).sum := by decide
  have hdescent : baseEnd_5561967 < baseStart_5561967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561985 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_5561985 : Nat := 118140960795 + 5561985 * 2 ^ 59
def prefixEnd_5561985 : Nat := 4983230072969 + 3 ^ 40 * 5561985 * 2
def baseEnd_5561985 : Nat := 2855971698097526441808403

theorem tailTrace_5561985 : CollatzResearch.WordTrace tailWord_5561985 prefixEnd_5561985 2855971698097526441808403 := by
  unfold tailWord_5561985
  simp only [CollatzResearch.WordTrace]
  refine ⟨202862258754885731256799409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135241505836590487504532939 202862258754885731256799409)
  ·
    refine ⟨152146694066164298442599557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202862258754885731256799409 152146694066164298442599557)
    ·
      refine ⟨28527505137405805957987417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152146694066164298442599557 28527505137405805957987417)
      ·
        refine ⟨21395628853054354468490563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28527505137405805957987417 21395628853054354468490563)
        ·
          refine ⟨32093443279581531702735845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21395628853054354468490563 32093443279581531702735845)
          ·
            refine ⟨6017520614921537194262971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32093443279581531702735845 6017520614921537194262971)
            ·
              refine ⟨9026280922382305791394457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017520614921537194262971 9026280922382305791394457)
              ·
                refine ⟨6769710691786729343545843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9026280922382305791394457 6769710691786729343545843)
                ·
                  refine ⟨10154566037680094015318765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769710691786729343545843 10154566037680094015318765)
                  ·
                    refine ⟨3807962264130035255744537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10154566037680094015318765 3807962264130035255744537)
                    ·
                      refine ⟨2855971698097526441808403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807962264130035255744537 2855971698097526441808403)
                      ·
                        rfl

theorem cell23_5561985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_5561985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561985 prefixEnd_5561985 := by exact prefixLift 5561985
  have htrace : WordTrace (prefixWord ++ tailWord_5561985) baseStart_5561985 baseEnd_5561985 := by
    simpa [prefixWord, tailWord_5561985, baseEnd_5561985] using wordTrace_append hprefix tailTrace_5561985
  have hstable : (prefixWord ++ tailWord_5561985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561985).length < 2 ^ (prefixWord ++ tailWord_5561985).sum := by decide
  have hdescent : baseEnd_5561985 < baseStart_5561985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561987 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 9]
def baseStart_5561987 : Nat := 118140960795 + 5561987 * 2 ^ 59
def prefixEnd_5561987 : Nat := 4983230072969 + 3 ^ 40 * 5561987 * 2
def baseEnd_5561987 : Nat := 317330302784315048220377

theorem tailTrace_5561987 : CollatzResearch.WordTrace tailWord_5561987 prefixEnd_5561987 317330302784315048220377 := by
  unfold tailWord_5561987
  simp only [CollatzResearch.WordTrace]
  refine ⟨202862331700878485598372215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135241554467252323732248143 202862331700878485598372215)
  ·
    refine ⟨304293497551317728397558323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202862331700878485598372215 304293497551317728397558323)
    ·
      refine ⟨456440246326976592596337485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304293497551317728397558323 456440246326976592596337485)
      ·
        refine ⟨171165092372616222223626557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456440246326976592596337485 171165092372616222223626557)
        ·
          refine ⟨64186909639731083333859959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171165092372616222223626557 64186909639731083333859959)
          ·
            refine ⟨96280364459596625000789939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64186909639731083333859959 96280364459596625000789939)
            ·
              refine ⟨144420546689394937501184909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96280364459596625000789939 144420546689394937501184909)
              ·
                refine ⟨54157705008523101562944341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144420546689394937501184909 54157705008523101562944341)
                ·
                  refine ⟨317330302784315048220377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54157705008523101562944341 317330302784315048220377)
                  ·
                    rfl

theorem cell23_5561987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 9].length) (baseStart_5561987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561987 prefixEnd_5561987 := by exact prefixLift 5561987
  have htrace : WordTrace (prefixWord ++ tailWord_5561987) baseStart_5561987 baseEnd_5561987 := by
    simpa [prefixWord, tailWord_5561987, baseEnd_5561987] using wordTrace_append hprefix tailTrace_5561987
  have hstable : (prefixWord ++ tailWord_5561987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561987).length < 2 ^ (prefixWord ++ tailWord_5561987).sum := by decide
  have hdescent : baseEnd_5561987 < baseStart_5561987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5561998 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5561998 : Nat := 118140960795 + 5561998 * 2 ^ 59
def prefixEnd_5561998 : Nat := 4983230072969 + 3 ^ 40 * 5561998 * 2
def baseEnd_5561998 : Nat := 2855978373346034890945843

theorem tailTrace_5561998 : CollatzResearch.WordTrace tailWord_5561998 prefixEnd_5561998 2855978373346034890945843 := by
  unfold tailWord_5561998
  simp only [CollatzResearch.WordTrace]
  refine ⟨25357841612979829309627831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135241821935892422984681765 25357841612979829309627831)
  ·
    refine ⟨38036762419469743964441747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25357841612979829309627831 38036762419469743964441747)
    ·
      refine ⟨57055143629204615946662621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38036762419469743964441747 57055143629204615946662621)
      ·
        refine ⟨21395678860951730979998483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57055143629204615946662621 21395678860951730979998483)
        ·
          refine ⟨32093518291427596469997725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21395678860951730979998483 32093518291427596469997725)
          ·
            refine ⟨12035069359285348676249147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32093518291427596469997725 12035069359285348676249147)
            ·
              refine ⟨18052604038928023014373721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035069359285348676249147 18052604038928023014373721)
              ·
                refine ⟨13539453029196017260780291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18052604038928023014373721 13539453029196017260780291)
                ·
                  refine ⟨20309179543794025891170437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13539453029196017260780291 20309179543794025891170437)
                  ·
                    refine ⟨3807971164461379854594457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20309179543794025891170437 3807971164461379854594457)
                    ·
                      refine ⟨2855978373346034890945843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807971164461379854594457 2855978373346034890945843)
                      ·
                        rfl

theorem cell23_5561998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5561998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5561998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5561998 prefixEnd_5561998 := by exact prefixLift 5561998
  have htrace : WordTrace (prefixWord ++ tailWord_5561998) baseStart_5561998 baseEnd_5561998 := by
    simpa [prefixWord, tailWord_5561998, baseEnd_5561998] using wordTrace_append hprefix tailTrace_5561998
  have hstable : (prefixWord ++ tailWord_5561998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5561998).length < 2 ^ (prefixWord ++ tailWord_5561998).sum := by decide
  have hdescent : baseEnd_5561998 < baseStart_5561998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5561998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562002 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5562002 : Nat := 118140960795 + 5562002 * 2 ^ 59
def prefixEnd_5562002 : Nat := 4983230072969 + 3 ^ 40 * 5562002 * 2
def baseEnd_5562002 : Nat := 2855980427268652875295825

theorem tailTrace_5562002 : CollatzResearch.WordTrace tailWord_5562002 prefixEnd_5562002 2855980427268652875295825 := by
  unfold tailWord_5562002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715719698956035790042065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135241919197216095440112173 50715719698956035790042065)
  ·
    refine ⟨38036789774217026842531549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50715719698956035790042065 38036789774217026842531549)
    ·
      refine ⟨14263796165331385065949331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38036789774217026842531549 14263796165331385065949331)
      ·
        refine ⟨21395694247997077598923997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14263796165331385065949331 21395694247997077598923997)
        ·
          refine ⟨8023385342998904099596499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21395694247997077598923997 8023385342998904099596499)
          ·
            refine ⟨12035078014498356149394749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023385342998904099596499 12035078014498356149394749)
            ·
              refine ⟨4513154255436883556023031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12035078014498356149394749 4513154255436883556023031)
              ·
                refine ⟨6769731383155325334034547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513154255436883556023031 6769731383155325334034547)
                ·
                  refine ⟨10154597074732988001051821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769731383155325334034547 10154597074732988001051821)
                  ·
                    refine ⟨3807973903024870500394433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10154597074732988001051821 3807973903024870500394433)
                    ·
                      refine ⟨2855980427268652875295825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3807973903024870500394433 2855980427268652875295825)
                      ·
                        rfl

theorem cell23_5562002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5562002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562002 prefixEnd_5562002 := by exact prefixLift 5562002
  have htrace : WordTrace (prefixWord ++ tailWord_5562002) baseStart_5562002 baseEnd_5562002 := by
    simpa [prefixWord, tailWord_5562002, baseEnd_5562002] using wordTrace_append hprefix tailTrace_5562002
  have hstable : (prefixWord ++ tailWord_5562002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562002).length < 2 ^ (prefixWord ++ tailWord_5562002).sum := by decide
  have hdescent : baseEnd_5562002 < baseStart_5562002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562034 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_5562034 : Nat := 118140960795 + 5562034 * 2 ^ 59
def prefixEnd_5562034 : Nat := 4983230072969 + 3 ^ 40 * 5562034 * 2
def baseEnd_5562034 : Nat := 951998952883198916698559

theorem tailTrace_5562034 : CollatzResearch.WordTrace tailWord_5562034 prefixEnd_5562034 951998952883198916698559 := by
  unfold tailWord_5562034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50716011482927053156333289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135242697287805475083555437 50716011482927053156333289)
  ·
    refine ⟨38037008612195289867249967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50716011482927053156333289 38037008612195289867249967)
    ·
      refine ⟨57055512918292934800874951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38037008612195289867249967 57055512918292934800874951)
      ·
        refine ⟨85583269377439402201312427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57055512918292934800874951 85583269377439402201312427)
        ·
          refine ⟨128374904066159103301968641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85583269377439402201312427 128374904066159103301968641)
          ·
            refine ⟨96281178049619327476476481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128374904066159103301968641 96281178049619327476476481)
            ·
              refine ⟨72210883537214495607357361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96281178049619327476476481 72210883537214495607357361)
              ·
                refine ⟨54158162652910871705518021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72210883537214495607357361 54158162652910871705518021)
                ·
                  refine ⟨10154655497420788444784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54158162652910871705518021 10154655497420788444784629)
                  ·
                    refine ⟨951998952883198916698559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10154655497420788444784629 951998952883198916698559)
                    ·
                      rfl

theorem cell23_5562034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_5562034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562034 prefixEnd_5562034 := by exact prefixLift 5562034
  have htrace : WordTrace (prefixWord ++ tailWord_5562034) baseStart_5562034 baseEnd_5562034 := by
    simpa [prefixWord, tailWord_5562034, baseEnd_5562034] using wordTrace_append hprefix tailTrace_5562034
  have hstable : (prefixWord ++ tailWord_5562034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562034).length < 2 ^ (prefixWord ++ tailWord_5562034).sum := by decide
  have hdescent : baseEnd_5562034 < baseStart_5562034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562038 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5562038 : Nat := 118140960795 + 5562038 * 2 ^ 59
def prefixEnd_5562038 : Nat := 4983230072969 + 3 ^ 40 * 5562038 * 2
def baseEnd_5562038 : Nat := 317333212508023859382851

theorem tailTrace_5562038 : CollatzResearch.WordTrace tailWord_5562038 prefixEnd_5562038 317333212508023859382851 := by
  unfold tailWord_5562038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679011988980857581779923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135242794549129147538985845 12679011988980857581779923)
  ·
    refine ⟨19018517983471286372669885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679011988980857581779923 19018517983471286372669885)
    ·
      refine ⟨7131944243801732389751207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19018517983471286372669885 7131944243801732389751207)
      ·
        refine ⟨10697916365702598584626811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131944243801732389751207 10697916365702598584626811)
        ·
          refine ⟨16046874548553897876940217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697916365702598584626811 16046874548553897876940217)
          ·
            refine ⟨12035155911415423407705163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16046874548553897876940217 12035155911415423407705163)
            ·
              refine ⟨18052733867123135111557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035155911415423407705163 18052733867123135111557745)
              ·
                refine ⟨13539550400342351333668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18052733867123135111557745 13539550400342351333668309)
                ·
                  refine ⟨317333212508023859382851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13539550400342351333668309 317333212508023859382851)
                  ·
                    rfl

theorem cell23_5562038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5562038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562038 prefixEnd_5562038 := by exact prefixLift 5562038
  have htrace : WordTrace (prefixWord ++ tailWord_5562038) baseStart_5562038 baseEnd_5562038 := by
    simpa [prefixWord, tailWord_5562038, baseEnd_5562038] using wordTrace_append hprefix tailTrace_5562038
  have hstable : (prefixWord ++ tailWord_5562038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562038).length < 2 ^ (prefixWord ++ tailWord_5562038).sum := by decide
  have hdescent : baseEnd_5562038 < baseStart_5562038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562071 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_5562071 : Nat := 118140960795 + 5562071 * 2 ^ 59
def prefixEnd_5562071 : Nat := 4983230072969 + 3 ^ 40 * 5562071 * 2
def baseEnd_5562071 : Nat := 2856015857433813105333007

theorem tailTrace_5562071 : CollatzResearch.WordTrace tailWord_5562071 prefixEnd_5562071 2856015857433813105333007 := by
  unfold tailWord_5562071
  simp only [CollatzResearch.WordTrace]
  refine ⟨202865395432574167944430067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135243596955049445296286711 202865395432574167944430067)
  ·
    refine ⟨304298093148861251916645101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202865395432574167944430067 304298093148861251916645101)
    ·
      refine ⟨114111784930822969468741913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304298093148861251916645101 114111784930822969468741913)
      ·
        refine ⟨85583838698117227101556435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114111784930822969468741913 85583838698117227101556435)
        ·
          refine ⟨128375758047175840652334653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85583838698117227101556435 128375758047175840652334653)
          ·
            refine ⟨48140909267690940244625495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128375758047175840652334653 48140909267690940244625495)
            ·
              refine ⟨72211363901536410366938243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48140909267690940244625495 72211363901536410366938243)
              ·
                refine ⟨108317045852304615550407365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72211363901536410366938243 108317045852304615550407365)
                ·
                  refine ⟨20309446097307115415701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108317045852304615550407365 20309446097307115415701381)
                  ·
                    refine ⟨3808021143245084140444009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20309446097307115415701381 3808021143245084140444009)
                    ·
                      refine ⟨2856015857433813105333007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808021143245084140444009 2856015857433813105333007)
                      ·
                        rfl

theorem cell23_5562071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_5562071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562071 prefixEnd_5562071 := by exact prefixLift 5562071
  have htrace : WordTrace (prefixWord ++ tailWord_5562071) baseStart_5562071 baseEnd_5562071 := by
    simpa [prefixWord, tailWord_5562071, baseEnd_5562071] using wordTrace_append hprefix tailTrace_5562071
  have hstable : (prefixWord ++ tailWord_5562071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562071).length < 2 ^ (prefixWord ++ tailWord_5562071).sum := by decide
  have hdescent : baseEnd_5562071 < baseStart_5562071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562084 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_5562084 : Nat := 118140960795 + 5562084 * 2 ^ 59
def prefixEnd_5562084 : Nat := 4983230072969 + 3 ^ 40 * 5562084 * 2
def baseEnd_5562084 : Nat := 2856022532682321554470447

theorem tailTrace_5562084 : CollatzResearch.WordTrace tailWord_5562084 prefixEnd_5562084 2856022532682321554470447 := by
  unfold tailWord_5562084
  simp only [CollatzResearch.WordTrace]
  refine ⟨101432934790763535582326653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135243913054351380776435537 101432934790763535582326653)
  ·
    refine ⟨38037350546536325843372495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101432934790763535582326653 38037350546536325843372495)
    ·
      refine ⟨57056025819804488765058743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38037350546536325843372495 57056025819804488765058743)
      ·
        refine ⟨85584038729706733147588115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57056025819804488765058743 85584038729706733147588115)
        ·
          refine ⟨128376058094560099721382173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85584038729706733147588115 128376058094560099721382173)
          ·
            refine ⟨48141021785460037395518315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128376058094560099721382173 48141021785460037395518315)
            ·
              refine ⟨72211532678190056093277473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48141021785460037395518315 72211532678190056093277473)
              ·
                refine ⟨54158649508642542069958105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72211532678190056093277473 54158649508642542069958105)
                ·
                  refine ⟨40618987131481906552468579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54158649508642542069958105 40618987131481906552468579)
                  ·
                    refine ⟨60928480697222859828702869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40618987131481906552468579 60928480697222859828702869)
                    ·
                      refine ⟨2856022532682321554470447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60928480697222859828702869 2856022532682321554470447)
                      ·
                        rfl

theorem cell23_5562084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_5562084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562084 prefixEnd_5562084 := by exact prefixLift 5562084
  have htrace : WordTrace (prefixWord ++ tailWord_5562084) baseStart_5562084 baseEnd_5562084 := by
    simpa [prefixWord, tailWord_5562084, baseEnd_5562084] using wordTrace_append hprefix tailTrace_5562084
  have hstable : (prefixWord ++ tailWord_5562084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562084).length < 2 ^ (prefixWord ++ tailWord_5562084).sum := by decide
  have hdescent : baseEnd_5562084 < baseStart_5562084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562088 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5562088 : Nat := 118140960795 + 5562088 * 2 ^ 59
def prefixEnd_5562088 : Nat := 4983230072969 + 3 ^ 40 * 5562088 * 2
def baseEnd_5562088 : Nat := 2856024586604939538820429

theorem tailTrace_5562088 : CollatzResearch.WordTrace tailWord_5562088 prefixEnd_5562088 2856024586604939538820429 := by
  unfold tailWord_5562088
  simp only [CollatzResearch.WordTrace]
  refine ⟨101433007736756289923899459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135244010315675053231865945 101433007736756289923899459)
  ·
    refine ⟨152149511605134434885849189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101433007736756289923899459 152149511605134434885849189)
    ·
      refine ⟨28528033425962706541096723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152149511605134434885849189 28528033425962706541096723)
      ·
        refine ⟨42792050138944059811645085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28528033425962706541096723 42792050138944059811645085)
        ·
          refine ⟨16047018802104022429366907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42792050138944059811645085 16047018802104022429366907)
          ·
            refine ⟨24070528203156033644050361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16047018802104022429366907 24070528203156033644050361)
            ·
              refine ⟨18052896152367025233037771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24070528203156033644050361 18052896152367025233037771)
              ·
                refine ⟨27079344228550537849556657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18052896152367025233037771 27079344228550537849556657)
                ·
                  refine ⟨20309508171412903387167493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27079344228550537849556657 20309508171412903387167493)
                  ·
                    refine ⟨3808032782139919385093905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20309508171412903387167493 3808032782139919385093905)
                    ·
                      refine ⟨2856024586604939538820429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808032782139919385093905 2856024586604939538820429)
                      ·
                        rfl

theorem cell23_5562088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5562088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562088 prefixEnd_5562088 := by exact prefixLift 5562088
  have htrace : WordTrace (prefixWord ++ tailWord_5562088) baseStart_5562088 baseEnd_5562088 := by
    simpa [prefixWord, tailWord_5562088, baseEnd_5562088] using wordTrace_append hprefix tailTrace_5562088
  have hstable : (prefixWord ++ tailWord_5562088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562088).length < 2 ^ (prefixWord ++ tailWord_5562088).sum := by decide
  have hdescent : baseEnd_5562088 < baseStart_5562088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562131 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 5, 2]
def baseStart_5562131 : Nat := 118140960795 + 5562131 * 2 ^ 59
def prefixEnd_5562131 : Nat := 4983230072969 + 3 ^ 40 * 5562131 * 2
def baseEnd_5562131 : Nat := 2856046666273082870582731

theorem tailTrace_5562131 : CollatzResearch.WordTrace tailWord_5562131 prefixEnd_5562131 2856046666273082870582731 := by
  unfold tailWord_5562131
  simp only [CollatzResearch.WordTrace]
  refine ⟨202867583812356798191614247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135245055874904532127742831 202867583812356798191614247)
  ·
    refine ⟨304301375718535197287421371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202867583812356798191614247 304301375718535197287421371)
    ·
      refine ⟨456452063577802795931132057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304301375718535197287421371 456452063577802795931132057)
      ·
        refine ⟨342339047683352096948349043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456452063577802795931132057 342339047683352096948349043)
        ·
          refine ⟨513508571525028145422523565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342339047683352096948349043 513508571525028145422523565)
          ·
            refine ⟨192565714321885554533446337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513508571525028145422523565 192565714321885554533446337)
            ·
              refine ⟨144424285741414165900084753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192565714321885554533446337 144424285741414165900084753)
              ·
                refine ⟨108318214306060624425063565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144424285741414165900084753 108318214306060624425063565)
                ·
                  refine ⟨40619330364772734159398837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108318214306060624425063565 40619330364772734159398837)
                  ·
                    refine ⟨3808062221697443827443641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40619330364772734159398837 3808062221697443827443641)
                    ·
                      refine ⟨2856046666273082870582731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808062221697443827443641 2856046666273082870582731)
                      ·
                        rfl

theorem cell23_5562131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5, 2].length) (baseStart_5562131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562131 prefixEnd_5562131 := by exact prefixLift 5562131
  have htrace : WordTrace (prefixWord ++ tailWord_5562131) baseStart_5562131 baseEnd_5562131 := by
    simpa [prefixWord, tailWord_5562131, baseEnd_5562131] using wordTrace_append hprefix tailTrace_5562131
  have hstable : (prefixWord ++ tailWord_5562131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562131).length < 2 ^ (prefixWord ++ tailWord_5562131).sum := by decide
  have hdescent : baseEnd_5562131 < baseStart_5562131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562175 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 1, 5]
def baseStart_5562175 : Nat := 118140960795 + 5562175 * 2 ^ 59
def prefixEnd_5562175 : Nat := 4983230072969 + 3 ^ 40 * 5562175 * 2
def baseEnd_5562175 : Nat := 952023086473960232810843

theorem tailTrace_5562175 : CollatzResearch.WordTrace tailWord_5562175 prefixEnd_5562175 952023086473960232810843 := by
  unfold tailWord_5562175
  simp only [CollatzResearch.WordTrace]
  refine ⟨202869188624197393706215979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135246125749464929137477319 202869188624197393706215979)
  ·
    refine ⟨304303782936296090559323969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202869188624197393706215979 304303782936296090559323969)
    ·
      refine ⟨228227837202222067919492977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304303782936296090559323969 228227837202222067919492977)
      ·
        refine ⟨171170877901666550939619733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228227837202222067919492977 171170877901666550939619733)
        ·
          refine ⟨8023634901640619575294675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171170877901666550939619733 8023634901640619575294675)
          ·
            refine ⟨12035452352460929362942013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023634901640619575294675 12035452352460929362942013)
            ·
              refine ⟨4513294632172848511103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12035452352460929362942013 4513294632172848511103255)
              ·
                refine ⟨6769941948259272766654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513294632172848511103255 6769941948259272766654883)
                ·
                  refine ⟨10154912922388909149982325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769941948259272766654883 10154912922388909149982325)
                  ·
                    refine ⟨952023086473960232810843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10154912922388909149982325 952023086473960232810843)
                    ·
                      rfl

theorem cell23_5562175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_5562175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562175 prefixEnd_5562175 := by exact prefixLift 5562175
  have htrace : WordTrace (prefixWord ++ tailWord_5562175) baseStart_5562175 baseEnd_5562175 := by
    simpa [prefixWord, tailWord_5562175, baseEnd_5562175] using wordTrace_append hprefix tailTrace_5562175
  have hstable : (prefixWord ++ tailWord_5562175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562175).length < 2 ^ (prefixWord ++ tailWord_5562175).sum := by decide
  have hdescent : baseEnd_5562175 < baseStart_5562175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562184 : List Nat := [2, 1, 3, 1, 1, 15]
def baseStart_5562184 : Nat := 118140960795 + 5562184 * 2 ^ 59
def prefixEnd_5562184 : Nat := 4983230072969 + 3 ^ 40 * 5562184 * 2
def baseEnd_5562184 : Nat := 11753390455752144704609

theorem tailTrace_5562184 : CollatzResearch.WordTrace tailWord_5562184 prefixEnd_5562184 11753390455752144704609 := by
  unfold tailWord_5562184
  simp only [CollatzResearch.WordTrace]
  refine ⟨101434758440582394121646803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135246344587443192162195737 101434758440582394121646803)
  ·
    refine ⟨152152137660873591182470205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101434758440582394121646803 152152137660873591182470205)
    ·
      refine ⟨57057051622827596693426327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152152137660873591182470205 57057051622827596693426327)
      ·
        refine ⟨85585577434241395040139491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57057051622827596693426327 85585577434241395040139491)
        ·
          refine ⟨128378366151362092560209237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85585577434241395040139491 128378366151362092560209237)
          ·
            refine ⟨11753390455752144704609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 128378366151362092560209237 11753390455752144704609)
            ·
              rfl

theorem cell23_5562184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 15].length) (baseStart_5562184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562184 prefixEnd_5562184 := by exact prefixLift 5562184
  have htrace : WordTrace (prefixWord ++ tailWord_5562184) baseStart_5562184 baseEnd_5562184 := by
    simpa [prefixWord, tailWord_5562184, baseEnd_5562184] using wordTrace_append hprefix tailTrace_5562184
  have hstable : (prefixWord ++ tailWord_5562184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562184).length < 2 ^ (prefixWord ++ tailWord_5562184).sum := by decide
  have hdescent : baseEnd_5562184 < baseStart_5562184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562189 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5562189 : Nat := 118140960795 + 5562189 * 2 ^ 59
def prefixEnd_5562189 : Nat := 4983230072969 + 3 ^ 40 * 5562189 * 2
def baseEnd_5562189 : Nat := 2856076448151043643657465

theorem tailTrace_5562189 : CollatzResearch.WordTrace tailWord_5562189 prefixEnd_5562189 2856076448151043643657465 := by
  unfold tailWord_5562189
  simp only [CollatzResearch.WordTrace]
  refine ⟨202869699246146674097225621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135246466164097782731483747 202869699246146674097225621)
  ·
    refine ⟨9509517152163125348307451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202869699246146674097225621 9509517152163125348307451)
    ·
      refine ⟨14264275728244688022461177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9509517152163125348307451 14264275728244688022461177)
      ·
        refine ⟨10698206796183516016845883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14264275728244688022461177 10698206796183516016845883)
        ·
          refine ⟨16047310194275274025268825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698206796183516016845883 16047310194275274025268825)
          ·
            refine ⟨12035482645706455518951619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16047310194275274025268825 12035482645706455518951619)
            ·
              refine ⟨18053223968559683278427429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035482645706455518951619 18053223968559683278427429)
              ·
                refine ⟨3384979494104940614705143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18053223968559683278427429 3384979494104940614705143)
                ·
                  refine ⟨5077469241157410922057715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384979494104940614705143 5077469241157410922057715)
                  ·
                    refine ⟨7616203861736116383086573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077469241157410922057715 7616203861736116383086573)
                    ·
                      refine ⟨2856076448151043643657465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7616203861736116383086573 2856076448151043643657465)
                      ·
                        rfl

theorem cell23_5562189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5562189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562189 prefixEnd_5562189 := by exact prefixLift 5562189
  have htrace : WordTrace (prefixWord ++ tailWord_5562189) baseStart_5562189 baseEnd_5562189 := by
    simpa [prefixWord, tailWord_5562189, baseEnd_5562189] using wordTrace_append hprefix tailTrace_5562189
  have hstable : (prefixWord ++ tailWord_5562189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562189).length < 2 ^ (prefixWord ++ tailWord_5562189).sum := by decide
  have hdescent : baseEnd_5562189 < baseStart_5562189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562208 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_5562208 : Nat := 118140960795 + 5562208 * 2 ^ 59
def prefixEnd_5562208 : Nat := 4983230072969 + 3 ^ 40 * 5562208 * 2
def baseEnd_5562208 : Nat := 2856086204283479069319877

theorem tailTrace_5562208 : CollatzResearch.WordTrace tailWord_5562208 prefixEnd_5562208 2856086204283479069319877 := by
  unfold tailWord_5562208
  simp only [CollatzResearch.WordTrace]
  refine ⟨101435196116538920171083639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135246928155385226894778185 101435196116538920171083639)
  ·
    refine ⟨152152794174808380256625459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101435196116538920171083639 152152794174808380256625459)
    ·
      refine ⟨228229191262212570384938189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152152794174808380256625459 228229191262212570384938189)
      ·
        refine ⟨85585946723329713894351821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228229191262212570384938189 85585946723329713894351821)
        ·
          refine ⟨32094730021248642710381933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85585946723329713894351821 32094730021248642710381933)
          ·
            refine ⟨12035523757968241016393225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32094730021248642710381933 12035523757968241016393225)
            ·
              refine ⟨9026642818476180762294919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12035523757968241016393225 9026642818476180762294919)
              ·
                refine ⟨13539964227714271143442379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9026642818476180762294919 13539964227714271143442379)
                ·
                  refine ⟨20309946341571406715163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13539964227714271143442379 20309946341571406715163569)
                  ·
                    refine ⟨15232459756178555036372677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20309946341571406715163569 15232459756178555036372677)
                    ·
                      refine ⟨2856086204283479069319877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15232459756178555036372677 2856086204283479069319877)
                      ·
                        rfl

theorem cell23_5562208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_5562208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562208 prefixEnd_5562208 := by exact prefixLift 5562208
  have htrace : WordTrace (prefixWord ++ tailWord_5562208) baseStart_5562208 baseEnd_5562208 := by
    simpa [prefixWord, tailWord_5562208, baseEnd_5562208] using wordTrace_append hprefix tailTrace_5562208
  have hstable : (prefixWord ++ tailWord_5562208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562208).length < 2 ^ (prefixWord ++ tailWord_5562208).sum := by decide
  have hdescent : baseEnd_5562208 < baseStart_5562208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562212 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_5562212 : Nat := 118140960795 + 5562212 * 2 ^ 59
def prefixEnd_5562212 : Nat := 4983230072969 + 3 ^ 40 * 5562212 * 2
def baseEnd_5562212 : Nat := 2856088258206097053669859

theorem tailTrace_5562212 : CollatzResearch.WordTrace tailWord_5562212 prefixEnd_5562212 2856088258206097053669859 := by
  unfold tailWord_5562212
  simp only [CollatzResearch.WordTrace]
  refine ⟨101435269062531674512656445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135247025416708899350208593 101435269062531674512656445)
  ·
    refine ⟨38038225898449377942246167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101435269062531674512656445 38038225898449377942246167)
    ·
      refine ⟨57057338847674066913369251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38038225898449377942246167 57057338847674066913369251)
      ·
        refine ⟨85586008271511100370053877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57057338847674066913369251 85586008271511100370053877)
        ·
          refine ⟨8023688275454165659692551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85586008271511100370053877 8023688275454165659692551)
          ·
            refine ⟨12035532413181248489538827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023688275454165659692551 12035532413181248489538827)
            ·
              refine ⟨18053298619771872734308241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035532413181248489538827 18053298619771872734308241)
              ·
                refine ⟨13539973964828904550731181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18053298619771872734308241 13539973964828904550731181)
                ·
                  refine ⟨5077490236810839206524193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13539973964828904550731181 5077490236810839206524193)
                  ·
                    refine ⟨3808117677608129404893145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077490236810839206524193 3808117677608129404893145)
                    ·
                      refine ⟨2856088258206097053669859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808117677608129404893145 2856088258206097053669859)
                      ·
                        rfl

theorem cell23_5562212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_5562212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562212 prefixEnd_5562212 := by exact prefixLift 5562212
  have htrace : WordTrace (prefixWord ++ tailWord_5562212) baseStart_5562212 baseEnd_5562212 := by
    simpa [prefixWord, tailWord_5562212, baseEnd_5562212] using wordTrace_append hprefix tailTrace_5562212
  have hstable : (prefixWord ++ tailWord_5562212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562212).length < 2 ^ (prefixWord ++ tailWord_5562212).sum := by decide
  have hdescent : baseEnd_5562212 < baseStart_5562212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562229 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5562229 : Nat := 118140960795 + 5562229 * 2 ^ 59
def prefixEnd_5562229 : Nat := 4983230072969 + 3 ^ 40 * 5562229 * 2
def baseEnd_5562229 : Nat := 2856096987377223487157281

theorem tailTrace_5562229 : CollatzResearch.WordTrace tailWord_5562229 prefixEnd_5562229 2856096987377223487157281 := by
  unfold tailWord_5562229
  simp only [CollatzResearch.WordTrace]
  refine ⟨202871158166001760928681741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135247438777334507285787827 202871158166001760928681741)
  ·
    refine ⟨76076684312250660348255653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202871158166001760928681741 76076684312250660348255653)
    ·
      refine ⟨14264378308546998815297935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76076684312250660348255653 14264378308546998815297935)
      ·
        refine ⟨21396567462820498222946903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14264378308546998815297935 21396567462820498222946903)
        ·
          refine ⟨32094851194230747334420355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21396567462820498222946903 32094851194230747334420355)
          ·
            refine ⟨48142276791346121001630533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32094851194230747334420355 48142276791346121001630533)
            ·
              refine ⟨9026676898377397687805725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48142276791346121001630533 9026676898377397687805725)
              ·
                refine ⟨3385003836891524132927147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9026676898377397687805725 3385003836891524132927147)
                ·
                  refine ⟨5077505755337286199390721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385003836891524132927147 5077505755337286199390721)
                  ·
                    refine ⟨3808129316502964649543041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077505755337286199390721 3808129316502964649543041)
                    ·
                      refine ⟨2856096987377223487157281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808129316502964649543041 2856096987377223487157281)
                      ·
                        rfl

theorem cell23_5562229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5562229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562229 prefixEnd_5562229 := by exact prefixLift 5562229
  have htrace : WordTrace (prefixWord ++ tailWord_5562229) baseStart_5562229 baseEnd_5562229 := by
    simpa [prefixWord, tailWord_5562229, baseEnd_5562229] using wordTrace_append hprefix tailTrace_5562229
  have hstable : (prefixWord ++ tailWord_5562229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562229).length < 2 ^ (prefixWord ++ tailWord_5562229).sum := by decide
  have hdescent : baseEnd_5562229 < baseStart_5562229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562261 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5562261 : Nat := 118140960795 + 5562261 * 2 ^ 59
def prefixEnd_5562261 : Nat := 4983230072969 + 3 ^ 40 * 5562261 * 2
def baseEnd_5562261 : Nat := 952037806252722453985711

theorem tailTrace_5562261 : CollatzResearch.WordTrace tailWord_5562261 prefixEnd_5562261 952037806252722453985711 := by
  unfold tailWord_5562261
  simp only [CollatzResearch.WordTrace]
  refine ⟨202872325301885830393846637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135248216867923886929231091 202872325301885830393846637)
  ·
    refine ⟨76077121988207186397692489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202872325301885830393846637 76077121988207186397692489)
    ·
      refine ⟨57057841491155389798269367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76077121988207186397692489 57057841491155389798269367)
      ·
        refine ⟨85586762236733084697404051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57057841491155389798269367 85586762236733084697404051)
        ·
          refine ⟨128380143355099627046106077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85586762236733084697404051 128380143355099627046106077)
          ·
            refine ⟨48142553758162360142289779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128380143355099627046106077 48142553758162360142289779)
            ·
              refine ⟨72213830637243540213434669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48142553758162360142289779 72213830637243540213434669)
              ·
                refine ⟨27080186488966327580038001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72213830637243540213434669 27080186488966327580038001)
                ·
                  refine ⟨20310139866724745685028501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27080186488966327580038001 20310139866724745685028501)
                  ·
                    refine ⟨952037806252722453985711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20310139866724745685028501 952037806252722453985711)
                    ·
                      rfl

theorem cell23_5562261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5562261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562261 prefixEnd_5562261 := by exact prefixLift 5562261
  have htrace : WordTrace (prefixWord ++ tailWord_5562261) baseStart_5562261 baseEnd_5562261 := by
    simpa [prefixWord, tailWord_5562261, baseEnd_5562261] using wordTrace_append hprefix tailTrace_5562261
  have hstable : (prefixWord ++ tailWord_5562261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562261).length < 2 ^ (prefixWord ++ tailWord_5562261).sum := by decide
  have hdescent : baseEnd_5562261 < baseStart_5562261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562280 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5562280 : Nat := 118140960795 + 5562280 * 2 ^ 59
def prefixEnd_5562280 : Nat := 4983230072969 + 3 ^ 40 * 5562280 * 2
def baseEnd_5562280 : Nat := 2856123174890602787619547

theorem tailTrace_5562280 : CollatzResearch.WordTrace tailWord_5562280 prefixEnd_5562280 2856123174890602787619547 := by
  unfold tailWord_5562280
  simp only [CollatzResearch.WordTrace]
  refine ⟨101436509144408498319394147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135248678859211331092525529 101436509144408498319394147)
  ·
    refine ⟨152154763716612747479091221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101436509144408498319394147 152154763716612747479091221)
    ·
      refine ⟨7132254549216222538082401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152154763716612747479091221 7132254549216222538082401)
      ·
        refine ⟨5349190911912166903561801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132254549216222538082401 5349190911912166903561801)
        ·
          refine ⟨4011893183934125177671351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349190911912166903561801 4011893183934125177671351)
          ·
            refine ⟨6017839775901187766507027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011893183934125177671351 6017839775901187766507027)
            ·
              refine ⟨9026759663851781649760541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017839775901187766507027 9026759663851781649760541)
              ·
                refine ⟨3385034873944418118660203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9026759663851781649760541 3385034873944418118660203)
                ·
                  refine ⟨5077552310916627177990305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385034873944418118660203 5077552310916627177990305)
                  ·
                    refine ⟨3808164233187470383492729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077552310916627177990305 3808164233187470383492729)
                    ·
                      refine ⟨2856123174890602787619547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808164233187470383492729 2856123174890602787619547)
                      ·
                        rfl

theorem cell23_5562280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5562280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562280 prefixEnd_5562280 := by exact prefixLift 5562280
  have htrace : WordTrace (prefixWord ++ tailWord_5562280) baseStart_5562280 baseEnd_5562280 := by
    simpa [prefixWord, tailWord_5562280, baseEnd_5562280] using wordTrace_append hprefix tailTrace_5562280
  have hstable : (prefixWord ++ tailWord_5562280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562280).length < 2 ^ (prefixWord ++ tailWord_5562280).sum := by decide
  have hdescent : baseEnd_5562280 < baseStart_5562280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562281 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_5562281 : Nat := 118140960795 + 5562281 * 2 ^ 59
def prefixEnd_5562281 : Nat := 4983230072969 + 3 ^ 40 * 5562281 * 2
def baseEnd_5562281 : Nat := 2856123688371257283707041

theorem tailTrace_5562281 : CollatzResearch.WordTrace tailWord_5562281 prefixEnd_5562281 2856123688371257283707041 := by
  unfold tailWord_5562281
  simp only [CollatzResearch.WordTrace]
  refine ⟨202873054761813373809574697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135248703174542249206383131 202873054761813373809574697)
  ·
    refine ⟨152154791071360030357181023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202873054761813373809574697 152154791071360030357181023)
    ·
      refine ⟨228232186607040045535771535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152154791071360030357181023 228232186607040045535771535)
      ·
        refine ⟨342348279910560068303657303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228232186607040045535771535 342348279910560068303657303)
        ·
          refine ⟨513522419865840102455485955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342348279910560068303657303 513522419865840102455485955)
          ·
            refine ⟨770283629798760153683228933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513522419865840102455485955 770283629798760153683228933)
            ·
              refine ⟨144428180587267528815605425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 770283629798760153683228933 144428180587267528815605425)
              ·
                refine ⟨108321135440450646611704069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144428180587267528815605425 108321135440450646611704069)
                ·
                  refine ⟨20310212895084496239694513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108321135440450646611704069 20310212895084496239694513)
                  ·
                    refine ⟨15232659671313372179770885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20310212895084496239694513 15232659671313372179770885)
                    ·
                      refine ⟨2856123688371257283707041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15232659671313372179770885 2856123688371257283707041)
                      ·
                        rfl

theorem cell23_5562281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_5562281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562281 prefixEnd_5562281 := by exact prefixLift 5562281
  have htrace : WordTrace (prefixWord ++ tailWord_5562281) baseStart_5562281 baseEnd_5562281 := by
    simpa [prefixWord, tailWord_5562281, baseEnd_5562281] using wordTrace_append hprefix tailTrace_5562281
  have hstable : (prefixWord ++ tailWord_5562281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562281).length < 2 ^ (prefixWord ++ tailWord_5562281).sum := by decide
  have hdescent : baseEnd_5562281 < baseStart_5562281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562302 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_5562302 : Nat := 118140960795 + 5562302 * 2 ^ 59
def prefixEnd_5562302 : Nat := 4983230072969 + 3 ^ 40 * 5562302 * 2
def baseEnd_5562302 : Nat := 2856134471465001701544445

theorem tailTrace_5562302 : CollatzResearch.WordTrace tailWord_5562302 prefixEnd_5562302 2856134471465001701544445 := by
  unfold tailWord_5562302
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359227586842161799511145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135249213796491529597392773 25359227586842161799511145)
  ·
    refine ⟨19019420690131621349633359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25359227586842161799511145 19019420690131621349633359)
    ·
      refine ⟨28529131035197432024450039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19019420690131621349633359 28529131035197432024450039)
      ·
        refine ⟨42793696552796148036675059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28529131035197432024450039 42793696552796148036675059)
        ·
          refine ⟨64190544829194222055012589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42793696552796148036675059 64190544829194222055012589)
          ·
            refine ⟨24071454310947833270629721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64190544829194222055012589 24071454310947833270629721)
            ·
              refine ⟨18053590733210874952972291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24071454310947833270629721 18053590733210874952972291)
              ·
                refine ⟨27080386099816312429458437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18053590733210874952972291 27080386099816312429458437)
                ·
                  refine ⟨5077572393715558580523457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27080386099816312429458437 5077572393715558580523457)
                  ·
                    refine ⟨3808179295286668935392593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077572393715558580523457 3808179295286668935392593)
                    ·
                      refine ⟨2856134471465001701544445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808179295286668935392593 2856134471465001701544445)
                      ·
                        rfl

theorem cell23_5562302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_5562302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562302 prefixEnd_5562302 := by exact prefixLift 5562302
  have htrace : WordTrace (prefixWord ++ tailWord_5562302) baseStart_5562302 baseEnd_5562302 := by
    simpa [prefixWord, tailWord_5562302, baseEnd_5562302] using wordTrace_append hprefix tailTrace_5562302
  have hstable : (prefixWord ++ tailWord_5562302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562302).length < 2 ^ (prefixWord ++ tailWord_5562302).sum := by decide
  have hdescent : baseEnd_5562302 < baseStart_5562302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562318 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_5562318 : Nat := 118140960795 + 5562318 * 2 ^ 59
def prefixEnd_5562318 : Nat := 4983230072969 + 3 ^ 40 * 5562318 * 2
def baseEnd_5562318 : Nat := 2856142687155473638944371

theorem tailTrace_5562318 : CollatzResearch.WordTrace tailWord_5562318 prefixEnd_5562318 2856142687155473638944371 := by
  unfold tailWord_5562318
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359300532834916141083951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135249602841786219419114405 25359300532834916141083951)
  ·
    refine ⟨38038950799252374211625927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25359300532834916141083951 38038950799252374211625927)
    ·
      refine ⟨57058426198878561317438891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38038950799252374211625927 57058426198878561317438891)
      ·
        refine ⟨85587639298317841976158337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57058426198878561317438891 85587639298317841976158337)
        ·
          refine ⟨64190729473738381482118753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85587639298317841976158337 64190729473738381482118753)
          ·
            refine ⟨48143047105303786111589065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64190729473738381482118753 48143047105303786111589065)
            ·
              refine ⟨36107285328977839583691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48143047105303786111589065 36107285328977839583691799)
              ·
                refine ⟨54160927993466759375537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36107285328977839583691799 54160927993466759375537699)
                ·
                  refine ⟨81241391990200139063306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54160927993466759375537699 81241391990200139063306549)
                  ·
                    refine ⟨7616380499081263037184989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81241391990200139063306549 7616380499081263037184989)
                    ·
                      refine ⟨2856142687155473638944371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7616380499081263037184989 2856142687155473638944371)
                      ·
                        rfl

theorem cell23_5562318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_5562318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562318 prefixEnd_5562318 := by exact prefixLift 5562318
  have htrace : WordTrace (prefixWord ++ tailWord_5562318) baseStart_5562318 baseEnd_5562318 := by
    simpa [prefixWord, tailWord_5562318, baseEnd_5562318] using wordTrace_append hprefix tailTrace_5562318
  have hstable : (prefixWord ++ tailWord_5562318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562318).length < 2 ^ (prefixWord ++ tailWord_5562318).sum := by decide
  have hdescent : baseEnd_5562318 < baseStart_5562318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562321 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_5562321 : Nat := 118140960795 + 5562321 * 2 ^ 59
def prefixEnd_5562321 : Nat := 4983230072969 + 3 ^ 40 * 5562321 * 2
def baseEnd_5562321 : Nat := 952048075865812375735619

theorem tailTrace_5562321 : CollatzResearch.WordTrace tailWord_5562321 prefixEnd_5562321 952048075865812375735619 := by
  unfold tailWord_5562321
  simp only [CollatzResearch.WordTrace]
  refine ⟨202874513681668460641030817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135249675787778973760687211 202874513681668460641030817)
  ·
    refine ⟨152155885261251345480773113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202874513681668460641030817 152155885261251345480773113)
    ·
      refine ⟨114116913945938509110579835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152155885261251345480773113 114116913945938509110579835)
      ·
        refine ⟨171175370918907763665869753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114116913945938509110579835 171175370918907763665869753)
        ·
          refine ⟨128381528189180822749402315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171175370918907763665869753 128381528189180822749402315)
          ·
            refine ⟨192572292283771234124103473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128381528189180822749402315 192572292283771234124103473)
            ·
              refine ⟨144429219212828425593077605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192572292283771234124103473 144429219212828425593077605)
              ·
                refine ⟨27080478602405329798702051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144429219212828425593077605 27080478602405329798702051)
                ·
                  refine ⟨40620717903607994698053077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27080478602405329798702051 40620717903607994698053077)
                  ·
                    refine ⟨952048075865812375735619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40620717903607994698053077 952048075865812375735619)
                    ·
                      rfl

theorem cell23_5562321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_5562321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562321 prefixEnd_5562321 := by exact prefixLift 5562321
  have htrace : WordTrace (prefixWord ++ tailWord_5562321) baseStart_5562321 baseEnd_5562321 := by
    simpa [prefixWord, tailWord_5562321, baseEnd_5562321] using wordTrace_append hprefix tailTrace_5562321
  have hstable : (prefixWord ++ tailWord_5562321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562321).length < 2 ^ (prefixWord ++ tailWord_5562321).sum := by decide
  have hdescent : baseEnd_5562321 < baseStart_5562321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562375 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5562375 : Nat := 118140960795 + 5562375 * 2 ^ 59
def prefixEnd_5562375 : Nat := 4983230072969 + 3 ^ 40 * 5562375 * 2
def baseEnd_5562375 : Nat := 2856171955552779915931609

theorem tailTrace_5562375 : CollatzResearch.WordTrace tailWord_5562375 prefixEnd_5562375 2856171955552779915931609 := by
  unfold tailWord_5562375
  simp only [CollatzResearch.WordTrace]
  refine ⟨202876483223472827863496579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135250988815648551908997719 202876483223472827863496579)
  ·
    refine ⟨304314724835209241795244869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202876483223472827863496579 304314724835209241795244869)
    ·
      refine ⟨57059010906601732836608413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304314724835209241795244869 57059010906601732836608413)
      ·
        refine ⟨21397129089975649813728155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57059010906601732836608413 21397129089975649813728155)
        ·
          refine ⟨32095693634963474720592233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21397129089975649813728155 32095693634963474720592233)
          ·
            refine ⟨24071770226222606040444175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32095693634963474720592233 24071770226222606040444175)
            ·
              refine ⟨36107655339333909060666263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24071770226222606040444175 36107655339333909060666263)
              ·
                refine ⟨54161483009000863590999395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36107655339333909060666263 54161483009000863590999395)
                ·
                  refine ⟨81242224513501295386499093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54161483009000863590999395 81242224513501295386499093)
                  ·
                    refine ⟨3808229274070373221242145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81242224513501295386499093 3808229274070373221242145)
                    ·
                      refine ⟨2856171955552779915931609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808229274070373221242145 2856171955552779915931609)
                      ·
                        rfl

theorem cell23_5562375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5562375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562375 prefixEnd_5562375 := by exact prefixLift 5562375
  have htrace : WordTrace (prefixWord ++ tailWord_5562375) baseStart_5562375 baseEnd_5562375 := by
    simpa [prefixWord, tailWord_5562375, baseEnd_5562375] using wordTrace_append hprefix tailTrace_5562375
  have hstable : (prefixWord ++ tailWord_5562375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562375).length < 2 ^ (prefixWord ++ tailWord_5562375).sum := by decide
  have hdescent : baseEnd_5562375 < baseStart_5562375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562418 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5562418 : Nat := 118140960795 + 5562418 * 2 ^ 59
def prefixEnd_5562418 : Nat := 4983230072969 + 3 ^ 40 * 5562418 * 2
def baseEnd_5562418 : Nat := 2856194035220923247693911

theorem tailTrace_5562418 : CollatzResearch.WordTrace tailWord_5562418 prefixEnd_5562418 2856194035220923247693911 := by
  unfold tailWord_5562418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50719512890579261551827977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135252034374878030804874605 50719512890579261551827977)
  ·
    refine ⟨38039634667934446163870983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50719512890579261551827977 38039634667934446163870983)
    ·
      refine ⟨57059452001901669245806475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38039634667934446163870983 57059452001901669245806475)
      ·
        refine ⟨85589178002852503868709713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57059452001901669245806475 85589178002852503868709713)
        ·
          refine ⟨64191883502139377901532285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85589178002852503868709713 64191883502139377901532285)
          ·
            refine ⟨24071956313302266713074607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64191883502139377901532285 24071956313302266713074607)
            ·
              refine ⟨36107934469953400069611911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24071956313302266713074607 36107934469953400069611911)
              ·
                refine ⟨54161901704930100104417867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36107934469953400069611911 54161901704930100104417867)
                ·
                  refine ⟨81242852557395150156626801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54161901704930100104417867 81242852557395150156626801)
                  ·
                    refine ⟨60932139418046362617470101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81242852557395150156626801 60932139418046362617470101)
                    ·
                      refine ⟨2856194035220923247693911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60932139418046362617470101 2856194035220923247693911)
                      ·
                        rfl

theorem cell23_5562418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5562418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562418 prefixEnd_5562418 := by exact prefixLift 5562418
  have htrace : WordTrace (prefixWord ++ tailWord_5562418) baseStart_5562418 baseEnd_5562418 := by
    simpa [prefixWord, tailWord_5562418, baseEnd_5562418] using wordTrace_append hprefix tailTrace_5562418
  have hstable : (prefixWord ++ tailWord_5562418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562418).length < 2 ^ (prefixWord ++ tailWord_5562418).sum := by decide
  have hdescent : baseEnd_5562418 < baseStart_5562418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562435 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 6, 3, 2]
def baseStart_5562435 : Nat := 118140960795 + 5562435 * 2 ^ 59
def prefixEnd_5562435 : Nat := 4983230072969 + 3 ^ 40 * 5562435 * 2
def baseEnd_5562435 : Nat := 2856202764392049681181333

theorem tailTrace_5562435 : CollatzResearch.WordTrace tailWord_5562435 prefixEnd_5562435 2856202764392049681181333 := by
  unfold tailWord_5562435
  simp only [CollatzResearch.WordTrace]
  refine ⟨202878671603255458110680759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135252447735503638740453839 202878671603255458110680759)
  ·
    refine ⟨304318007404883187166021139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202878671603255458110680759 304318007404883187166021139)
    ·
      refine ⟨456477011107324780749031709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304318007404883187166021139 456477011107324780749031709)
      ·
        refine ⟨171178879165246792780886891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456477011107324780749031709 171178879165246792780886891)
        ·
          refine ⟨256768318747870189171330337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171178879165246792780886891 256768318747870189171330337)
          ·
            refine ⟨192576239060902641878497753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256768318747870189171330337 192576239060902641878497753)
            ·
              refine ⟨144432179295676981408873315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192576239060902641878497753 144432179295676981408873315)
              ·
                refine ⟨216648268943515472113309973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144432179295676981408873315 216648268943515472113309973)
                ·
                  refine ⟨10155387606727287755311405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216648268943515472113309973 10155387606727287755311405)
                  ·
                    refine ⟨3808270352522732908241777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10155387606727287755311405 3808270352522732908241777)
                    ·
                      refine ⟨2856202764392049681181333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808270352522732908241777 2856202764392049681181333)
                      ·
                        rfl

theorem cell23_5562435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_5562435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562435 prefixEnd_5562435 := by exact prefixLift 5562435
  have htrace : WordTrace (prefixWord ++ tailWord_5562435) baseStart_5562435 baseEnd_5562435 := by
    simpa [prefixWord, tailWord_5562435, baseEnd_5562435] using wordTrace_append hprefix tailTrace_5562435
  have hstable : (prefixWord ++ tailWord_5562435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562435).length < 2 ^ (prefixWord ++ tailWord_5562435).sum := by decide
  have hdescent : baseEnd_5562435 < baseStart_5562435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562452 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_5562452 : Nat := 118140960795 + 5562452 * 2 ^ 59
def prefixEnd_5562452 : Nat := 4983230072969 + 3 ^ 40 * 5562452 * 2
def baseEnd_5562452 : Nat := 2856211493563176114668755

theorem tailTrace_5562452 : CollatzResearch.WordTrace tailWord_5562452 prefixEnd_5562452 2856211493563176114668755 := by
  unfold tailWord_5562452
  simp only [CollatzResearch.WordTrace]
  refine ⟨101439645822096935007024805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135252861096129246676033073 101439645822096935007024805)
  ·
    refine ⟨19019933591643175313817151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101439645822096935007024805 19019933591643175313817151)
    ·
      refine ⟨28529900387464762970725727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19019933591643175313817151 28529900387464762970725727)
      ·
        refine ⟨42794850581197144456088591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28529900387464762970725727 42794850581197144456088591)
        ·
          refine ⟨64192275871795716684132887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42794850581197144456088591 64192275871795716684132887)
          ·
            refine ⟨96288413807693575026199331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64192275871795716684132887 96288413807693575026199331)
            ·
              refine ⟨144432620711540362539298997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96288413807693575026199331 144432620711540362539298997)
              ·
                refine ⟨13540558191706908988059281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144432620711540362539298997 13540558191706908988059281)
                ·
                  refine ⟨10155418643780181741044461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13540558191706908988059281 10155418643780181741044461)
                  ·
                    refine ⟨3808281991417568152891673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10155418643780181741044461 3808281991417568152891673)
                    ·
                      refine ⟨2856211493563176114668755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808281991417568152891673 2856211493563176114668755)
                      ·
                        rfl

theorem cell23_5562452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_5562452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562452 prefixEnd_5562452 := by exact prefixLift 5562452
  have htrace : WordTrace (prefixWord ++ tailWord_5562452) baseStart_5562452 baseEnd_5562452 := by
    simpa [prefixWord, tailWord_5562452, baseEnd_5562452] using wordTrace_append hprefix tailTrace_5562452
  have hstable : (prefixWord ++ tailWord_5562452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562452).length < 2 ^ (prefixWord ++ tailWord_5562452).sum := by decide
  have hdescent : baseEnd_5562452 < baseStart_5562452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562458 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_5562458 : Nat := 118140960795 + 5562458 * 2 ^ 59
def prefixEnd_5562458 : Nat := 4983230072969 + 3 ^ 40 * 5562458 * 2
def baseEnd_5562458 : Nat := 952071524815701030397909

theorem tailTrace_5562458 : CollatzResearch.WordTrace tailWord_5562458 prefixEnd_5562458 952071524815701030397909 := by
  unfold tailWord_5562458
  simp only [CollatzResearch.WordTrace]
  refine ⟨50719877620543033259692007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135253006988114755359178685 50719877620543033259692007)
  ·
    refine ⟨76079816430814549889538011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50719877620543033259692007 76079816430814549889538011)
    ·
      refine ⟨114119724646221824834307017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76079816430814549889538011 114119724646221824834307017)
      ·
        refine ⟨85589793484666368625730263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114119724646221824834307017 85589793484666368625730263)
        ·
          refine ⟨128384690226999552938595395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85589793484666368625730263 128384690226999552938595395)
          ·
            refine ⟨192577035340499329407893093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128384690226999552938595395 192577035340499329407893093)
            ·
              refine ⟨36108194126343624263979955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192577035340499329407893093 36108194126343624263979955)
              ·
                refine ⟨54162291189515436395969933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36108194126343624263979955 54162291189515436395969933)
                ·
                  refine ⟨20310859196068288648488725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54162291189515436395969933 20310859196068288648488725)
                  ·
                    refine ⟨952071524815701030397909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20310859196068288648488725 952071524815701030397909)
                    ·
                      rfl

theorem cell23_5562458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_5562458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562458 prefixEnd_5562458 := by exact prefixLift 5562458
  have htrace : WordTrace (prefixWord ++ tailWord_5562458) baseStart_5562458 baseEnd_5562458 := by
    simpa [prefixWord, tailWord_5562458, baseEnd_5562458] using wordTrace_append hprefix tailTrace_5562458
  have hstable : (prefixWord ++ tailWord_5562458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562458).length < 2 ^ (prefixWord ++ tailWord_5562458).sum := by decide
  have hdescent : baseEnd_5562458 < baseStart_5562458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562476 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_5562476 : Nat := 118140960795 + 5562476 * 2 ^ 59
def prefixEnd_5562476 : Nat := 4983230072969 + 3 ^ 40 * 5562476 * 2
def baseEnd_5562476 : Nat := 2856223817098884020768645

theorem tailTrace_5562476 : CollatzResearch.WordTrace tailWord_5562476 prefixEnd_5562476 2856223817098884020768645 := by
  unfold tailWord_5562476
  simp only [CollatzResearch.WordTrace]
  refine ⟨101440083498053461056461641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135253444664071281408615521 101440083498053461056461641)
  ·
    refine ⟨76080062623540095792346231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101440083498053461056461641 76080062623540095792346231)
    ·
      refine ⟨114120093935310143688519347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76080062623540095792346231 114120093935310143688519347)
      ·
        refine ⟨171180140902965215532779021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114120093935310143688519347 171180140902965215532779021)
        ·
          refine ⟨64192552838611955824792133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171180140902965215532779021 64192552838611955824792133)
          ·
            refine ⟨12036103657239741717148525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64192552838611955824792133 12036103657239741717148525)
            ·
              refine ⟨4513538871464903143930697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12036103657239741717148525 4513538871464903143930697)
              ·
                refine ⟨3385154153598677357948023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513538871464903143930697 3385154153598677357948023)
                ·
                  refine ⟨5077731230398016036922035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385154153598677357948023 5077731230398016036922035)
                  ·
                    refine ⟨7616596845597024055383053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077731230398016036922035 7616596845597024055383053)
                    ·
                      refine ⟨2856223817098884020768645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7616596845597024055383053 2856223817098884020768645)
                      ·
                        rfl

theorem cell23_5562476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_5562476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562476 prefixEnd_5562476 := by exact prefixLift 5562476
  have htrace : WordTrace (prefixWord ++ tailWord_5562476) baseStart_5562476 baseEnd_5562476 := by
    simpa [prefixWord, tailWord_5562476, baseEnd_5562476] using wordTrace_append hprefix tailTrace_5562476
  have hstable : (prefixWord ++ tailWord_5562476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562476).length < 2 ^ (prefixWord ++ tailWord_5562476).sum := by decide
  have hdescent : baseEnd_5562476 < baseStart_5562476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562492 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5562492 : Nat := 118140960795 + 5562492 * 2 ^ 59
def prefixEnd_5562492 : Nat := 4983230072969 + 3 ^ 40 * 5562492 * 2
def baseEnd_5562492 : Nat := 952077344263118652722857

theorem tailTrace_5562492 : CollatzResearch.WordTrace tailWord_5562492 prefixEnd_5562492 952077344263118652722857 := by
  unfold tailWord_5562492
  simp only [CollatzResearch.WordTrace]
  refine ⟨101440375282024478422752865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135253833709365971230337153 101440375282024478422752865)
  ·
    refine ⟨76080281461518358817064649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101440375282024478422752865 76080281461518358817064649)
    ·
      refine ⟨57060211096138769112798487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76080281461518358817064649 57060211096138769112798487)
      ·
        refine ⟨85590316644208153669197731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57060211096138769112798487 85590316644208153669197731)
        ·
          refine ⟨128385474966312230503796597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85590316644208153669197731 128385474966312230503796597)
          ·
            refine ⟨12036138278091771609730931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128385474966312230503796597 12036138278091771609730931)
            ·
              refine ⟨18054207417137657414596397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036138278091771609730931 18054207417137657414596397)
              ·
                refine ⟨6770327781426621530473649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18054207417137657414596397 6770327781426621530473649)
                ·
                  refine ⟨5077745836069966147855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6770327781426621530473649 5077745836069966147855237)
                  ·
                    refine ⟨952077344263118652722857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077745836069966147855237 952077344263118652722857)
                    ·
                      rfl

theorem cell23_5562492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5562492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562492 prefixEnd_5562492 := by exact prefixLift 5562492
  have htrace : WordTrace (prefixWord ++ tailWord_5562492) baseStart_5562492 baseEnd_5562492 := by
    simpa [prefixWord, tailWord_5562492, baseEnd_5562492] using wordTrace_append hprefix tailTrace_5562492
  have hstable : (prefixWord ++ tailWord_5562492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562492).length < 2 ^ (prefixWord ++ tailWord_5562492).sum := by decide
  have hdescent : baseEnd_5562492 < baseStart_5562492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562519 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_5562519 : Nat := 118140960795 + 5562519 * 2 ^ 59
def prefixEnd_5562519 : Nat := 4983230072969 + 3 ^ 40 * 5562519 * 2
def baseEnd_5562519 : Nat := 2856245896767027352530947

theorem tailTrace_5562519 : CollatzResearch.WordTrace tailWord_5562519 prefixEnd_5562519 2856245896767027352530947 := by
  unfold tailWord_5562519
  simp only [CollatzResearch.WordTrace]
  refine ⟨202881735334951140456738611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135254490223300760304492407 202881735334951140456738611)
  ·
    refine ⟨304322603002426710685107917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202881735334951140456738611 304322603002426710685107917)
    ·
      refine ⟨114120976125910016506915469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304322603002426710685107917 114120976125910016506915469)
      ·
        refine ⟨42795366047216256190093301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114120976125910016506915469 42795366047216256190093301)
        ·
          refine ⟨4012065566926524017821247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42795366047216256190093301 4012065566926524017821247)
          ·
            refine ⟨6018098350389786026731871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012065566926524017821247 6018098350389786026731871)
            ·
              refine ⟨9027147525584679040097807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018098350389786026731871 9027147525584679040097807)
              ·
                refine ⟨13540721288377018560146711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9027147525584679040097807 13540721288377018560146711)
                ·
                  refine ⟨20311081932565527840220067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13540721288377018560146711 20311081932565527840220067)
                  ·
                    refine ⟨30466622898848291760330101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20311081932565527840220067 30466622898848291760330101)
                    ·
                      refine ⟨2856245896767027352530947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30466622898848291760330101 2856245896767027352530947)
                      ·
                        rfl

theorem cell23_5562519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_5562519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562519 prefixEnd_5562519 := by exact prefixLift 5562519
  have htrace : WordTrace (prefixWord ++ tailWord_5562519) baseStart_5562519 baseEnd_5562519 := by
    simpa [prefixWord, tailWord_5562519, baseEnd_5562519] using wordTrace_append hprefix tailTrace_5562519
  have hstable : (prefixWord ++ tailWord_5562519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562519).length < 2 ^ (prefixWord ++ tailWord_5562519).sum := by decide
  have hdescent : baseEnd_5562519 < baseStart_5562519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562526 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5562526 : Nat := 118140960795 + 5562526 * 2 ^ 59
def prefixEnd_5562526 : Nat := 4983230072969 + 3 ^ 40 * 5562526 * 2
def baseEnd_5562526 : Nat := 952083163710536275047805

theorem tailTrace_5562526 : CollatzResearch.WordTrace tailWord_5562526 prefixEnd_5562526 952083163710536275047805 := by
  unfold tailWord_5562526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360248830740722581530429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135254660430617187101495621 25360248830740722581530429)
  ·
    refine ⟨9510093311527770968073911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25360248830740722581530429 9510093311527770968073911)
    ·
      refine ⟨14265139967291656452110867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510093311527770968073911 14265139967291656452110867)
      ·
        refine ⟨21397709950937484678166301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14265139967291656452110867 21397709950937484678166301)
        ·
          refine ⟨8024141231601556754312363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21397709950937484678166301 8024141231601556754312363)
          ·
            refine ⟨12036211847402335131468545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024141231601556754312363 12036211847402335131468545)
            ·
              refine ⟨9027158885551751348601409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12036211847402335131468545 9027158885551751348601409)
              ·
                refine ⟨6770369164163813511451057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9027158885551751348601409 6770369164163813511451057)
                ·
                  refine ⟨5077776873122860133588293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6770369164163813511451057 5077776873122860133588293)
                  ·
                    refine ⟨952083163710536275047805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077776873122860133588293 952083163710536275047805)
                    ·
                      rfl

theorem cell23_5562526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5562526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562526 prefixEnd_5562526 := by exact prefixLift 5562526
  have htrace : WordTrace (prefixWord ++ tailWord_5562526) baseStart_5562526 baseEnd_5562526 := by
    simpa [prefixWord, tailWord_5562526, baseEnd_5562526] using wordTrace_append hprefix tailTrace_5562526
  have hstable : (prefixWord ++ tailWord_5562526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562526).length < 2 ^ (prefixWord ++ tailWord_5562526).sum := by decide
  have hdescent : baseEnd_5562526 < baseStart_5562526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562585 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_5562585 : Nat := 118140960795 + 5562585 * 2 ^ 59
def prefixEnd_5562585 : Nat := 4983230072969 + 3 ^ 40 * 5562585 * 2
def baseEnd_5562585 : Nat := 2856279786490224094305643

theorem tailTrace_5562585 : CollatzResearch.WordTrace tailWord_5562585 prefixEnd_5562585 2856279786490224094305643 := by
  unfold tailWord_5562585
  simp only [CollatzResearch.WordTrace]
  refine ⟨202884142552712033728641209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135256095035141355819094139 202884142552712033728641209)
  ·
    refine ⟨152163106914534025296480907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202884142552712033728641209 152163106914534025296480907)
    ·
      refine ⟨228244660371801037944721361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152163106914534025296480907 228244660371801037944721361)
      ·
        refine ⟨171183495278850778458541021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228244660371801037944721361 171183495278850778458541021)
        ·
          refine ⟨64193810729569041921952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171183495278850778458541021 64193810729569041921952883)
          ·
            refine ⟨96290716094353562882929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64193810729569041921952883 96290716094353562882929325)
            ·
              refine ⟨36109018535382586081098497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96290716094353562882929325 36109018535382586081098497)
              ·
                refine ⟨27081763901536939560823873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36109018535382586081098497 27081763901536939560823873)
                ·
                  refine ⟨20311322926152704670617905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27081763901536939560823873 20311322926152704670617905)
                  ·
                    refine ⟨15233492194614528502963429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20311322926152704670617905 15233492194614528502963429)
                    ·
                      refine ⟨2856279786490224094305643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15233492194614528502963429 2856279786490224094305643)
                      ·
                        rfl

theorem cell23_5562585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_5562585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562585 prefixEnd_5562585 := by exact prefixLift 5562585
  have htrace : WordTrace (prefixWord ++ tailWord_5562585) baseStart_5562585 baseEnd_5562585 := by
    simpa [prefixWord, tailWord_5562585, baseEnd_5562585] using wordTrace_append hprefix tailTrace_5562585
  have hstable : (prefixWord ++ tailWord_5562585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562585).length < 2 ^ (prefixWord ++ tailWord_5562585).sum := by decide
  have hdescent : baseEnd_5562585 < baseStart_5562585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562625 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5562625 : Nat := 118140960795 + 5562625 * 2 ^ 59
def prefixEnd_5562625 : Nat := 4983230072969 + 3 ^ 40 * 5562625 * 2
def baseEnd_5562625 : Nat := 952100108572134645935153

theorem tailTrace_5562625 : CollatzResearch.WordTrace tailWord_5562625 prefixEnd_5562625 952100108572134645935153 := by
  unfold tailWord_5562625
  simp only [CollatzResearch.WordTrace]
  refine ⟨202885601472567120560097329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135257067648378080373398219 202885601472567120560097329)
  ·
    refine ⟨152164201104425340420072997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202885601472567120560097329 152164201104425340420072997)
    ·
      refine ⟨28530787707079751328763687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152164201104425340420072997 28530787707079751328763687)
      ·
        refine ⟨42796181560619626993145531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28530787707079751328763687 42796181560619626993145531)
        ·
          refine ⟨64194272340929440489718297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42796181560619626993145531 64194272340929440489718297)
          ·
            refine ⟨48145704255697080367288723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64194272340929440489718297 48145704255697080367288723)
            ·
              refine ⟨72218556383545620550933085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48145704255697080367288723 72218556383545620550933085)
              ·
                refine ⟨27081958643829607706599907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72218556383545620550933085 27081958643829607706599907)
                ·
                  refine ⟨40622937965744411559899861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27081958643829607706599907 40622937965744411559899861)
                  ·
                    refine ⟨952100108572134645935153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40622937965744411559899861 952100108572134645935153)
                    ·
                      rfl

theorem cell23_5562625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5562625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562625 prefixEnd_5562625 := by exact prefixLift 5562625
  have htrace : WordTrace (prefixWord ++ tailWord_5562625) baseStart_5562625 baseEnd_5562625 := by
    simpa [prefixWord, tailWord_5562625, baseEnd_5562625] using wordTrace_append hprefix tailTrace_5562625
  have hstable : (prefixWord ++ tailWord_5562625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562625).length < 2 ^ (prefixWord ++ tailWord_5562625).sum := by decide
  have hdescent : baseEnd_5562625 < baseStart_5562625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562635 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_5562635 : Nat := 118140960795 + 5562635 * 2 ^ 59
def prefixEnd_5562635 : Nat := 4983230072969 + 3 ^ 40 * 5562635 * 2
def baseEnd_5562635 : Nat := 2856305460522948898680413

theorem tailTrace_5562635 : CollatzResearch.WordTrace tailWord_5562635 prefixEnd_5562635 2856305460522948898680413 := by
  unfold tailWord_5562635
  simp only [CollatzResearch.WordTrace]
  refine ⟨202885966202530892267961359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135257310801687261511974239 202885966202530892267961359)
  ·
    refine ⟨304328949303796338401942039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202885966202530892267961359 304328949303796338401942039)
    ·
      refine ⟨456493423955694507602913059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304328949303796338401942039 456493423955694507602913059)
      ·
        refine ⟨684740135933541761404369589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456493423955694507602913059 684740135933541761404369589)
        ·
          refine ⟨64194387743769540131659649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 684740135933541761404369589 64194387743769540131659649)
          ·
            refine ⟨48145790807827155098744737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64194387743769540131659649 48145790807827155098744737)
            ·
              refine ⟨36109343105870366324058553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48145790807827155098744737 36109343105870366324058553)
              ·
                refine ⟨27082007329402774743043915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36109343105870366324058553 27082007329402774743043915)
                ·
                  refine ⟨40623010994104162114565873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27082007329402774743043915 40623010994104162114565873)
                  ·
                    refine ⟨30467258245578121585924405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40623010994104162114565873 30467258245578121585924405)
                    ·
                      refine ⟨2856305460522948898680413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30467258245578121585924405 2856305460522948898680413)
                      ·
                        rfl

theorem cell23_5562635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_5562635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562635 prefixEnd_5562635 := by exact prefixLift 5562635
  have htrace : WordTrace (prefixWord ++ tailWord_5562635) baseStart_5562635 baseEnd_5562635 := by
    simpa [prefixWord, tailWord_5562635, baseEnd_5562635] using wordTrace_append hprefix tailTrace_5562635
  have hstable : (prefixWord ++ tailWord_5562635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562635).length < 2 ^ (prefixWord ++ tailWord_5562635).sum := by decide
  have hdescent : baseEnd_5562635 < baseStart_5562635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562729 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_5562729 : Nat := 118140960795 + 5562729 * 2 ^ 59
def prefixEnd_5562729 : Nat := 4983230072969 + 3 ^ 40 * 5562729 * 2
def baseEnd_5562729 : Nat := 2856353727704471530904981

theorem tailTrace_5562729 : CollatzResearch.WordTrace tailWord_5562729 prefixEnd_5562729 2856353727704471530904981 := by
  unfold tailWord_5562729
  simp only [CollatzResearch.WordTrace]
  refine ⟨202889394664190346321883241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135259596442793564214588827 202889394664190346321883241)
  ·
    refine ⟨152167045998142759741412431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202889394664190346321883241 152167045998142759741412431)
    ·
      refine ⟨228250568997214139612118647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152167045998142759741412431 228250568997214139612118647)
      ·
        refine ⟨342375853495821209418177971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228250568997214139612118647 342375853495821209418177971)
        ·
          refine ⟨513563780243731814127266957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342375853495821209418177971 513563780243731814127266957)
          ·
            refine ⟨192586417591399430297725109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513563780243731814127266957 192586417591399430297725109)
            ·
              refine ⟨18054976649193696590411729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192586417591399430297725109 18054976649193696590411729)
              ·
                refine ⟨13541232486895272442808797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18054976649193696590411729 13541232486895272442808797)
                ·
                  refine ⟨5077962182585727166053299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13541232486895272442808797 5077962182585727166053299)
                  ·
                    refine ⟨7616943273878590749079949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077962182585727166053299 7616943273878590749079949)
                    ·
                      refine ⟨2856353727704471530904981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7616943273878590749079949 2856353727704471530904981)
                      ·
                        rfl

theorem cell23_5562729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_5562729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562729 prefixEnd_5562729 := by exact prefixLift 5562729
  have htrace : WordTrace (prefixWord ++ tailWord_5562729) baseStart_5562729 baseEnd_5562729 := by
    simpa [prefixWord, tailWord_5562729, baseEnd_5562729] using wordTrace_append hprefix tailTrace_5562729
  have hstable : (prefixWord ++ tailWord_5562729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562729).length < 2 ^ (prefixWord ++ tailWord_5562729).sum := by decide
  have hdescent : baseEnd_5562729 < baseStart_5562729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562749 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_5562749 : Nat := 118140960795 + 5562749 * 2 ^ 59
def prefixEnd_5562749 : Nat := 4983230072969 + 3 ^ 40 * 5562749 * 2
def baseEnd_5562749 : Nat := 952121332439187150884963

theorem tailTrace_5562749 : CollatzResearch.WordTrace tailWord_5562749 prefixEnd_5562749 952121332439187150884963 := by
  unfold tailWord_5562749
  simp only [CollatzResearch.WordTrace]
  refine ⟨202890124124117889737611301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135260082749411926491740867 202890124124117889737611301)
  ·
    refine ⟨38041898273272104325802119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202890124124117889737611301 38041898273272104325802119)
    ·
      refine ⟨57062847409908156488703179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38041898273272104325802119 57062847409908156488703179)
      ·
        refine ⟨85594271114862234733054769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57062847409908156488703179 85594271114862234733054769)
        ·
          refine ⟨64195703336146676049791077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85594271114862234733054769 64195703336146676049791077)
          ·
            refine ⟨12036694375527501759335827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64195703336146676049791077 12036694375527501759335827)
            ·
              refine ⟨18055041563291252639003741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036694375527501759335827 18055041563291252639003741)
              ·
                refine ⟨6770640586234219739626403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18055041563291252639003741 6770640586234219739626403)
                ·
                  refine ⟨10155960879351329609439605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6770640586234219739626403 10155960879351329609439605)
                  ·
                    refine ⟨952121332439187150884963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10155960879351329609439605 952121332439187150884963)
                    ·
                      rfl

theorem cell23_5562749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_5562749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562749 prefixEnd_5562749 := by exact prefixLift 5562749
  have htrace : WordTrace (prefixWord ++ tailWord_5562749) baseStart_5562749 baseEnd_5562749 := by
    simpa [prefixWord, tailWord_5562749, baseEnd_5562749] using wordTrace_append hprefix tailTrace_5562749
  have hstable : (prefixWord ++ tailWord_5562749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562749).length < 2 ^ (prefixWord ++ tailWord_5562749).sum := by decide
  have hdescent : baseEnd_5562749 < baseStart_5562749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562786 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_5562786 : Nat := 118140960795 + 5562786 * 2 ^ 59
def prefixEnd_5562786 : Nat := 4983230072969 + 3 ^ 40 * 5562786 * 2
def baseEnd_5562786 : Nat := 2856382996101777807892219

theorem tailTrace_5562786 : CollatzResearch.WordTrace tailWord_5562786 prefixEnd_5562786 2856382996101777807892219 := by
  unfold tailWord_5562786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50722868406245961264177053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135260982416655896704472141 50722868406245961264177053)
  ·
    refine ⟨19021075652342235474066395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50722868406245961264177053 19021075652342235474066395)
    ·
      refine ⟨28531613478513353211099593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19021075652342235474066395 28531613478513353211099593)
      ·
        refine ⟨21398710108885014908324695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28531613478513353211099593 21398710108885014908324695)
        ·
          refine ⟨32098065163327522362487043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21398710108885014908324695 32098065163327522362487043)
          ·
            refine ⟨48147097744991283543730565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32098065163327522362487043 48147097744991283543730565)
            ·
              refine ⟨9027580827185865664449481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48147097744991283543730565 9027580827185865664449481)
              ·
                refine ⟨6770685620389399248337111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9027580827185865664449481 6770685620389399248337111)
                ·
                  refine ⟨10156028430584098872505667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6770685620389399248337111 10156028430584098872505667)
                  ·
                    refine ⟨15234042645876148308758501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10156028430584098872505667 15234042645876148308758501)
                    ·
                      refine ⟨2856382996101777807892219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15234042645876148308758501 2856382996101777807892219)
                      ·
                        rfl

theorem cell23_5562786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_5562786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562786 prefixEnd_5562786 := by exact prefixLift 5562786
  have htrace : WordTrace (prefixWord ++ tailWord_5562786) baseStart_5562786 baseEnd_5562786 := by
    simpa [prefixWord, tailWord_5562786, baseEnd_5562786] using wordTrace_append hprefix tailTrace_5562786
  have hstable : (prefixWord ++ tailWord_5562786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562786).length < 2 ^ (prefixWord ++ tailWord_5562786).sum := by decide
  have hdescent : baseEnd_5562786 < baseStart_5562786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562797 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5562797 : Nat := 118140960795 + 5562797 * 2 ^ 59
def prefixEnd_5562797 : Nat := 4983230072969 + 3 ^ 40 * 5562797 * 2
def baseEnd_5562797 : Nat := 2856388644388977264854669

theorem tailTrace_5562797 : CollatzResearch.WordTrace tailWord_5562797 prefixEnd_5562797 2856388644388977264854669 := by
  unfold tailWord_5562797
  simp only [CollatzResearch.WordTrace]
  refine ⟨202891874827943993935358645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135261249885295995956905763 202891874827943993935358645)
  ·
    refine ⟨19021113265119749431439873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202891874827943993935358645 19021113265119749431439873)
    ·
      refine ⟨14265834948839812073579905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19021113265119749431439873 14265834948839812073579905)
      ·
        refine ⟨10699376211629859055184929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14265834948839812073579905 10699376211629859055184929)
        ·
          refine ⟨8024532158722394291388697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10699376211629859055184929 8024532158722394291388697)
          ·
            refine ⟨6018399119041795718541523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8024532158722394291388697 6018399119041795718541523)
            ·
              refine ⟨9027598678562693577812285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018399119041795718541523 9027598678562693577812285)
              ·
                refine ⟨3385349504461010091679607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9027598678562693577812285 3385349504461010091679607)
                ·
                  refine ⟨5078024256691515137519411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385349504461010091679607 5078024256691515137519411)
                  ·
                    refine ⟨7617036385037272706279117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5078024256691515137519411 7617036385037272706279117)
                    ·
                      refine ⟨2856388644388977264854669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7617036385037272706279117 2856388644388977264854669)
                      ·
                        rfl

theorem cell23_5562797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5562797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562797 prefixEnd_5562797 := by exact prefixLift 5562797
  have htrace : WordTrace (prefixWord ++ tailWord_5562797) baseStart_5562797 baseEnd_5562797 := by
    simpa [prefixWord, tailWord_5562797, baseEnd_5562797] using wordTrace_append hprefix tailTrace_5562797
  have hstable : (prefixWord ++ tailWord_5562797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562797).length < 2 ^ (prefixWord ++ tailWord_5562797).sum := by decide
  have hdescent : baseEnd_5562797 < baseStart_5562797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562852 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_5562852 : Nat := 118140960795 + 5562852 * 2 ^ 59
def prefixEnd_5562852 : Nat := 4983230072969 + 3 ^ 40 * 5562852 * 2
def baseEnd_5562852 : Nat := 952138961941658183222305

theorem tailTrace_5562852 : CollatzResearch.WordTrace tailWord_5562852 prefixEnd_5562852 952138961941658183222305 := by
  unfold tailWord_5562852
  simp only [CollatzResearch.WordTrace]
  refine ⟨101446940421372369164305405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135262587228496492219073873 101446940421372369164305405)
  ·
    refine ⟨38042602658014638436614527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101446940421372369164305405 38042602658014638436614527)
    ·
      refine ⟨57063903987021957654921791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38042602658014638436614527 57063903987021957654921791)
      ·
        refine ⟨85595855980532936482382687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57063903987021957654921791 85595855980532936482382687)
        ·
          refine ⟨128393783970799404723574031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85595855980532936482382687 128393783970799404723574031)
          ·
            refine ⟨192590675956199107085361047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128393783970799404723574031 192590675956199107085361047)
            ·
              refine ⟨288886013934298660628041571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192590675956199107085361047 288886013934298660628041571)
              ·
                refine ⟨433329020901447990942062357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288886013934298660628041571 433329020901447990942062357)
                ·
                  refine ⟨20312297854755374575409173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 433329020901447990942062357 20312297854755374575409173)
                  ·
                    refine ⟨952138961941658183222305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20312297854755374575409173 952138961941658183222305)
                    ·
                      rfl

theorem cell23_5562852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_5562852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562852 prefixEnd_5562852 := by exact prefixLift 5562852
  have htrace : WordTrace (prefixWord ++ tailWord_5562852) baseStart_5562852 baseEnd_5562852 := by
    simpa [prefixWord, tailWord_5562852, baseEnd_5562852] using wordTrace_append hprefix tailTrace_5562852
  have hstable : (prefixWord ++ tailWord_5562852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562852).length < 2 ^ (prefixWord ++ tailWord_5562852).sum := by decide
  have hdescent : baseEnd_5562852 < baseStart_5562852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562929 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_5562929 : Nat := 118140960795 + 5562929 * 2 ^ 59
def prefixEnd_5562929 : Nat := 4983230072969 + 3 ^ 40 * 5562929 * 2
def baseEnd_5562929 : Nat := 952152141278456916134687

theorem tailTrace_5562929 : CollatzResearch.WordTrace tailWord_5562929 prefixEnd_5562929 952152141278456916134687 := by
  unfold tailWord_5562929
  simp only [CollatzResearch.WordTrace]
  refine ⟨202896689263465780479163841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135264459508977186986109227 202896689263465780479163841)
  ·
    refine ⟨152172516947599335359372881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202896689263465780479163841 152172516947599335359372881)
    ·
      refine ⟨114129387710699501519529661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152172516947599335359372881 114129387710699501519529661)
      ·
        refine ⟨42798520391512313069823623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114129387710699501519529661 42798520391512313069823623)
        ·
          refine ⟨64197780587268469604735435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42798520391512313069823623 64197780587268469604735435)
          ·
            refine ⟨96296670880902704407103153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64197780587268469604735435 96296670880902704407103153)
            ·
              refine ⟨72222503160677028305327365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96296670880902704407103153 72222503160677028305327365)
              ·
                refine ⟨13541719342626942807248881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72222503160677028305327365 13541719342626942807248881)
                ·
                  refine ⟨10156289506970207105436661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13541719342626942807248881 10156289506970207105436661)
                  ·
                    refine ⟨952152141278456916134687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10156289506970207105436661 952152141278456916134687)
                    ·
                      rfl

theorem cell23_5562929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_5562929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562929 prefixEnd_5562929 := by exact prefixLift 5562929
  have htrace : WordTrace (prefixWord ++ tailWord_5562929) baseStart_5562929 baseEnd_5562929 := by
    simpa [prefixWord, tailWord_5562929, baseEnd_5562929] using wordTrace_append hprefix tailTrace_5562929
  have hstable : (prefixWord ++ tailWord_5562929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562929).length < 2 ^ (prefixWord ++ tailWord_5562929).sum := by decide
  have hdescent : baseEnd_5562929 < baseStart_5562929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5562949 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_5562949 : Nat := 118140960795 + 5562949 * 2 ^ 59
def prefixEnd_5562949 : Nat := 4983230072969 + 3 ^ 40 * 5562949 * 2
def baseEnd_5562949 : Nat := 2856466693448460670153969

theorem tailTrace_5562949 : CollatzResearch.WordTrace tailWord_5562949 prefixEnd_5562949 2856466693448460670153969 := by
  unfold tailWord_5562949
  simp only [CollatzResearch.WordTrace]
  refine ⟨202897418723393323894891901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135264945815595549263261267 202897418723393323894891901)
  ·
    refine ⟨76086532021272496460584463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202897418723393323894891901 76086532021272496460584463)
    ·
      refine ⟨114129798031908744690876695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76086532021272496460584463 114129798031908744690876695)
      ·
        refine ⟨171194697047863117036315043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114129798031908744690876695 171194697047863117036315043)
        ·
          refine ⟨256792045571794675554472565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171194697047863117036315043 256792045571794675554472565)
          ·
            refine ⟨24074254272355750833231803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256792045571794675554472565 24074254272355750833231803)
            ·
              refine ⟨36111381408533626249847705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24074254272355750833231803 36111381408533626249847705)
              ·
                refine ⟨27083536056400219687385779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36111381408533626249847705 27083536056400219687385779)
                ·
                  refine ⟨40625304084600329531078669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27083536056400219687385779 40625304084600329531078669)
                  ·
                    refine ⟨15234489031725123574154501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40625304084600329531078669 15234489031725123574154501)
                    ·
                      refine ⟨2856466693448460670153969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15234489031725123574154501 2856466693448460670153969)
                      ·
                        rfl

theorem cell23_5562949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_5562949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5562949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5562949 prefixEnd_5562949 := by exact prefixLift 5562949
  have htrace : WordTrace (prefixWord ++ tailWord_5562949) baseStart_5562949 baseEnd_5562949 := by
    simpa [prefixWord, tailWord_5562949, baseEnd_5562949] using wordTrace_append hprefix tailTrace_5562949
  have hstable : (prefixWord ++ tailWord_5562949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5562949).length < 2 ^ (prefixWord ++ tailWord_5562949).sum := by decide
  have hdescent : baseEnd_5562949 < baseStart_5562949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5562949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563056 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2]
def baseStart_5563056 : Nat := 118140960795 + 5563056 * 2 ^ 59
def prefixEnd_5563056 : Nat := 4983230072969 + 3 ^ 40 * 5563056 * 2
def baseEnd_5563056 : Nat := 2856521635878491751515977

theorem tailTrace_5563056 : CollatzResearch.WordTrace tailWord_5563056 prefixEnd_5563056 2856521635878491751515977 := by
  unfold tailWord_5563056
  simp only [CollatzResearch.WordTrace]
  refine ⟨101450660667002840584518511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135267547556003787446024681 101450660667002840584518511)
  ·
    refine ⟨152175991000504260876777767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101450660667002840584518511 152175991000504260876777767)
    ·
      refine ⟨228263986500756391315166651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152175991000504260876777767 228263986500756391315166651)
      ·
        refine ⟨342395979751134586972749977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228263986500756391315166651 342395979751134586972749977)
        ·
          refine ⟨256796984813350940229562483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342395979751134586972749977 256796984813350940229562483)
          ·
            refine ⟨385195477220026410344343725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256796984813350940229562483 385195477220026410344343725)
            ·
              refine ⟨144448303957509903879128897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385195477220026410344343725 144448303957509903879128897)
              ·
                refine ⟨108336227968132427909346673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144448303957509903879128897 108336227968132427909346673)
                ·
                  refine ⟨81252170976099320932010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108336227968132427909346673 81252170976099320932010005)
                  ·
                    refine ⟨3808695514504655668687969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81252170976099320932010005 3808695514504655668687969)
                    ·
                      refine ⟨2856521635878491751515977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808695514504655668687969 2856521635878491751515977)
                      ·
                        rfl

theorem cell23_5563056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2].length) (baseStart_5563056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563056 prefixEnd_5563056 := by exact prefixLift 5563056
  have htrace : WordTrace (prefixWord ++ tailWord_5563056) baseStart_5563056 baseEnd_5563056 := by
    simpa [prefixWord, tailWord_5563056, baseEnd_5563056] using wordTrace_append hprefix tailTrace_5563056
  have hstable : (prefixWord ++ tailWord_5563056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563056).length < 2 ^ (prefixWord ++ tailWord_5563056).sum := by decide
  have hdescent : baseEnd_5563056 < baseStart_5563056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563066 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_5563066 : Nat := 118140960795 + 5563066 * 2 ^ 59
def prefixEnd_5563066 : Nat := 4983230072969 + 3 ^ 40 * 5563066 * 2
def baseEnd_5563066 : Nat := 952175590228345570796977

theorem tailTrace_5563066 : CollatzResearch.WordTrace tailWord_5563066 prefixEnd_5563066 952175590228345570796977 := by
  unfold tailWord_5563066
  simp only [CollatzResearch.WordTrace]
  refine ⟨50725421515992363219225263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135267790709312968584600701 50725421515992363219225263)
  ·
    refine ⟨76088132273988544828837895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50725421515992363219225263 76088132273988544828837895)
    ·
      refine ⟨114132198410982817243256843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76088132273988544828837895 114132198410982817243256843)
      ·
        refine ⟨171198297616474225864885265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114132198410982817243256843 171198297616474225864885265)
        ·
          refine ⟨128398723212355669398663949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171198297616474225864885265 128398723212355669398663949)
          ·
            refine ⟨48149521204633376024498981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128398723212355669398663949 48149521204633376024498981)
            ·
              refine ⟨9028035225868758004593559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48149521204633376024498981 9028035225868758004593559)
              ·
                refine ⟨13542052838803137006890339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028035225868758004593559 13542052838803137006890339)
                ·
                  refine ⟨20313079258204705510335509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542052838803137006890339 20313079258204705510335509)
                  ·
                    refine ⟨952175590228345570796977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20313079258204705510335509 952175590228345570796977)
                    ·
                      rfl

theorem cell23_5563066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_5563066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563066 prefixEnd_5563066 := by exact prefixLift 5563066
  have htrace : WordTrace (prefixWord ++ tailWord_5563066) baseStart_5563066 baseEnd_5563066 := by
    simpa [prefixWord, tailWord_5563066, baseEnd_5563066] using wordTrace_append hprefix tailTrace_5563066
  have hstable : (prefixWord ++ tailWord_5563066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563066).length < 2 ^ (prefixWord ++ tailWord_5563066).sum := by decide
  have hdescent : baseEnd_5563066 < baseStart_5563066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563090 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5563090 : Nat := 118140960795 + 5563090 * 2 ^ 59
def prefixEnd_5563090 : Nat := 4983230072969 + 3 ^ 40 * 5563090 * 2
def baseEnd_5563090 : Nat := 2856539094220744618490821

theorem tailTrace_5563090 : CollatzResearch.WordTrace tailWord_5563090 prefixEnd_5563090 2856539094220744618490821 := by
  unfold tailWord_5563090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50725640353970626243943681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135268374277255003317183149 50725640353970626243943681)
  ·
    refine ⟨38044230265477969682957761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50725640353970626243943681 38044230265477969682957761)
    ·
      refine ⟨28533172699108477262218321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38044230265477969682957761 28533172699108477262218321)
      ·
        refine ⟨21399879524331357946663741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28533172699108477262218321 21399879524331357946663741)
        ·
          refine ⟨8024954821624259229998903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21399879524331357946663741 8024954821624259229998903)
          ·
            refine ⟨12037432232436388844998355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024954821624259229998903 12037432232436388844998355)
            ·
              refine ⟨18056148348654583267497533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12037432232436388844998355 18056148348654583267497533)
              ·
                refine ⟨6771055630745468725311575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18056148348654583267497533 6771055630745468725311575)
                ·
                  refine ⟨10156583446118203087967363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771055630745468725311575 10156583446118203087967363)
                  ·
                    refine ⟨15234875169177304631951045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10156583446118203087967363 15234875169177304631951045)
                    ·
                      refine ⟨2856539094220744618490821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15234875169177304631951045 2856539094220744618490821)
                      ·
                        rfl

theorem cell23_5563090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5563090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563090 prefixEnd_5563090 := by exact prefixLift 5563090
  have htrace : WordTrace (prefixWord ++ tailWord_5563090) baseStart_5563090 baseEnd_5563090 := by
    simpa [prefixWord, tailWord_5563090, baseEnd_5563090] using wordTrace_append hprefix tailTrace_5563090
  have hstable : (prefixWord ++ tailWord_5563090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563090).length < 2 ^ (prefixWord ++ tailWord_5563090).sum := by decide
  have hdescent : baseEnd_5563090 < baseStart_5563090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563100 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5563100 : Nat := 118140960795 + 5563100 * 2 ^ 59
def prefixEnd_5563100 : Nat := 4983230072969 + 3 ^ 40 * 5563100 * 2
def baseEnd_5563100 : Nat := 952181409675763193121925

theorem tailTrace_5563100 : CollatzResearch.WordTrace tailWord_5563100 prefixEnd_5563100 952181409675763193121925 := by
  unfold tailWord_5563100
  simp only [CollatzResearch.WordTrace]
  refine ⟨101451463072923138341819377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135268617430564184455759169 101451463072923138341819377)
  ·
    refine ⟨76088597304692353756364533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101451463072923138341819377 76088597304692353756364533)
    ·
      refine ⟨7133305997314908164659175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76088597304692353756364533 7133305997314908164659175)
      ·
        refine ⟨10699958995972362246988763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133305997314908164659175 10699958995972362246988763)
        ·
          refine ⟨16049938493958543370483145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699958995972362246988763 16049938493958543370483145)
          ·
            refine ⟨12037453870468907527862359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16049938493958543370483145 12037453870468907527862359)
            ·
              refine ⟨18056180805703361291793539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12037453870468907527862359 18056180805703361291793539)
              ·
                refine ⟨27084271208555041937690309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18056180805703361291793539 27084271208555041937690309)
                ·
                  refine ⟨5078300851604070363316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27084271208555041937690309 5078300851604070363316933)
                  ·
                    refine ⟨952181409675763193121925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078300851604070363316933 952181409675763193121925)
                    ·
                      rfl

theorem cell23_5563100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5563100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563100 prefixEnd_5563100 := by exact prefixLift 5563100
  have htrace : WordTrace (prefixWord ++ tailWord_5563100) baseStart_5563100 baseEnd_5563100 := by
    simpa [prefixWord, tailWord_5563100, baseEnd_5563100] using wordTrace_append hprefix tailTrace_5563100
  have hstable : (prefixWord ++ tailWord_5563100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563100).length < 2 ^ (prefixWord ++ tailWord_5563100).sum := by decide
  have hdescent : baseEnd_5563100 < baseStart_5563100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563107 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5563107 : Nat := 118140960795 + 5563107 * 2 ^ 59
def prefixEnd_5563107 : Nat := 4983230072969 + 3 ^ 40 * 5563107 * 2
def baseEnd_5563107 : Nat := 2856547823391871051978243

theorem tailTrace_5563107 : CollatzResearch.WordTrace tailWord_5563107 prefixEnd_5563107 2856547823391871051978243 := by
  unfold tailWord_5563107
  simp only [CollatzResearch.WordTrace]
  refine ⟨202903181456820916879143575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135268787637880611252762383 202903181456820916879143575)
  ·
    refine ⟨304354772185231375318715363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202903181456820916879143575 304354772185231375318715363)
    ·
      refine ⟨456532158277847062978073045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304354772185231375318715363 456532158277847062978073045)
      ·
        refine ⟨10699972459637040538548587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 456532158277847062978073045 10699972459637040538548587)
        ·
          refine ⟨16049958689455560807822881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699972459637040538548587 16049958689455560807822881)
          ·
            refine ⟨12037469017091670605867161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16049958689455560807822881 12037469017091670605867161)
            ·
              refine ⟨9028101762818752954400371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12037469017091670605867161 9028101762818752954400371)
              ·
                refine ⟨13542152644228129431600557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028101762818752954400371 13542152644228129431600557)
                ·
                  refine ⟨5078307241585548536850209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13542152644228129431600557 5078307241585548536850209)
                  ·
                    refine ⟨3808730431189161402637657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078307241585548536850209 3808730431189161402637657)
                    ·
                      refine ⟨2856547823391871051978243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808730431189161402637657 2856547823391871051978243)
                      ·
                        rfl

theorem cell23_5563107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5563107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563107 prefixEnd_5563107 := by exact prefixLift 5563107
  have htrace : WordTrace (prefixWord ++ tailWord_5563107) baseStart_5563107 baseEnd_5563107 := by
    simpa [prefixWord, tailWord_5563107, baseEnd_5563107] using wordTrace_append hprefix tailTrace_5563107
  have hstable : (prefixWord ++ tailWord_5563107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563107).length < 2 ^ (prefixWord ++ tailWord_5563107).sum := by decide
  have hdescent : baseEnd_5563107 < baseStart_5563107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563124 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5563124 : Nat := 118140960795 + 5563124 * 2 ^ 59
def prefixEnd_5563124 : Nat := 4983230072969 + 3 ^ 40 * 5563124 * 2
def baseEnd_5563124 : Nat := 2856556552562997485465665

theorem tailTrace_5563124 : CollatzResearch.WordTrace tailWord_5563124 prefixEnd_5563124 2856556552562997485465665 := by
  unfold tailWord_5563124
  simp only [CollatzResearch.WordTrace]
  refine ⟨101451900748879664391256213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135269200998506219188341617 101451900748879664391256213)
  ·
    refine ⟨4755557847603734268340135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101451900748879664391256213 4755557847603734268340135)
    ·
      refine ⟨7133336771405601402510203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755557847603734268340135 7133336771405601402510203)
      ·
        refine ⟨10700005157108402103765305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133336771405601402510203 10700005157108402103765305)
        ·
          refine ⟨8025003867831301577823979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10700005157108402103765305 8025003867831301577823979)
          ·
            refine ⟨12037505801746952366735969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025003867831301577823979 12037505801746952366735969)
            ·
              refine ⟨9028129351310214275051977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12037505801746952366735969 9028129351310214275051977)
              ·
                refine ⟨6771097013482660706288983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9028129351310214275051977 6771097013482660706288983)
                ·
                  refine ⟨10156645520223991059433475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771097013482660706288983 10156645520223991059433475)
                  ·
                    refine ⟨15234968280335986589150213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10156645520223991059433475 15234968280335986589150213)
                    ·
                      refine ⟨2856556552562997485465665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15234968280335986589150213 2856556552562997485465665)
                      ·
                        rfl

theorem cell23_5563124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5563124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563124 prefixEnd_5563124 := by exact prefixLift 5563124
  have htrace : WordTrace (prefixWord ++ tailWord_5563124) baseStart_5563124 baseEnd_5563124 := by
    simpa [prefixWord, tailWord_5563124, baseEnd_5563124] using wordTrace_append hprefix tailTrace_5563124
  have hstable : (prefixWord ++ tailWord_5563124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563124).length < 2 ^ (prefixWord ++ tailWord_5563124).sum := by decide
  have hdescent : baseEnd_5563124 < baseStart_5563124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563186 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_5563186 : Nat := 118140960795 + 5563186 * 2 ^ 59
def prefixEnd_5563186 : Nat := 4983230072969 + 3 ^ 40 * 5563186 * 2
def baseEnd_5563186 : Nat := 317398709818175138098931

theorem tailTrace_5563186 : CollatzResearch.WordTrace tailWord_5563186 prefixEnd_5563186 317398709818175138098931 := by
  unfold tailWord_5563186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50726515705883678342817353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135270708549023142247512941 50726515705883678342817353)
  ·
    refine ⟨38044886779412758757113015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50726515705883678342817353 38044886779412758757113015)
    ·
      refine ⟨57067330169119138135669523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38044886779412758757113015 57067330169119138135669523)
      ·
        refine ⟨85600995253678707203504285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57067330169119138135669523 85600995253678707203504285)
        ·
          refine ⟨32100373220129515201314107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85600995253678707203504285 32100373220129515201314107)
          ·
            refine ⟨48150559830194272801971161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32100373220129515201314107 48150559830194272801971161)
            ·
              refine ⟨36112919872645704601478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48150559830194272801971161 36112919872645704601478371)
              ·
                refine ⟨54169379808968556902217557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36112919872645704601478371 54169379808968556902217557)
                ·
                  refine ⟨317398709818175138098931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54169379808968556902217557 317398709818175138098931)
                  ·
                    rfl

theorem cell23_5563186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_5563186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563186 prefixEnd_5563186 := by exact prefixLift 5563186
  have htrace : WordTrace (prefixWord ++ tailWord_5563186) baseStart_5563186 baseEnd_5563186 := by
    simpa [prefixWord, tailWord_5563186, baseEnd_5563186] using wordTrace_append hprefix tailTrace_5563186
  have hstable : (prefixWord ++ tailWord_5563186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563186).length < 2 ^ (prefixWord ++ tailWord_5563186).sum := by decide
  have hdescent : baseEnd_5563186 < baseStart_5563186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563197 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5563197 : Nat := 118140960795 + 5563197 * 2 ^ 59
def prefixEnd_5563197 : Nat := 4983230072969 + 3 ^ 40 * 5563197 * 2
def baseEnd_5563197 : Nat := 2856594036650775699852829

theorem tailTrace_5563197 : CollatzResearch.WordTrace tailWord_5563197 prefixEnd_5563197 2856594036650775699852829 := by
  unfold tailWord_5563197
  simp only [CollatzResearch.WordTrace]
  refine ⟨202906464026494862249919845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135270976017663241499946563 202906464026494862249919845)
  ·
    refine ⟨38044962004967786671859971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202906464026494862249919845 38044962004967786671859971)
    ·
      refine ⟨57067443007451680007789957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38044962004967786671859971 57067443007451680007789957)
      ·
        refine ⟨10700145563897190001460617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57067443007451680007789957 10700145563897190001460617)
        ·
          refine ⟨8025109172922892501095463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10700145563897190001460617 8025109172922892501095463)
          ·
            refine ⟨12037663759384338751643195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025109172922892501095463 12037663759384338751643195)
            ·
              refine ⟨18056495639076508127464793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12037663759384338751643195 18056495639076508127464793)
              ·
                refine ⟨13542371729307381095598595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18056495639076508127464793 13542371729307381095598595)
                ·
                  refine ⟨20313557593961071643397893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542371729307381095598595 20313557593961071643397893)
                  ·
                    refine ⟨3808792048867700933137105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20313557593961071643397893 3808792048867700933137105)
                    ·
                      refine ⟨2856594036650775699852829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808792048867700933137105 2856594036650775699852829)
                      ·
                        rfl

theorem cell23_5563197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5563197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563197 prefixEnd_5563197 := by exact prefixLift 5563197
  have htrace : WordTrace (prefixWord ++ tailWord_5563197) baseStart_5563197 baseEnd_5563197 := by
    simpa [prefixWord, tailWord_5563197, baseEnd_5563197] using wordTrace_append hprefix tailTrace_5563197
  have hstable : (prefixWord ++ tailWord_5563197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563197).length < 2 ^ (prefixWord ++ tailWord_5563197).sum := by decide
  have hdescent : baseEnd_5563197 < baseStart_5563197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563201 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5563201 : Nat := 118140960795 + 5563201 * 2 ^ 59
def prefixEnd_5563201 : Nat := 4983230072969 + 3 ^ 40 * 5563201 * 2
def baseEnd_5563201 : Nat := 2856596090573393684202811

theorem tailTrace_5563201 : CollatzResearch.WordTrace tailWord_5563201 prefixEnd_5563201 2856596090573393684202811 := by
  unfold tailWord_5563201
  simp only [CollatzResearch.WordTrace]
  refine ⟨202906609918480370933065457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135271073278986913955376971 202906609918480370933065457)
  ·
    refine ⟨152179957438860278199799093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202906609918480370933065457 152179957438860278199799093)
    ·
      refine ⟨14266871009893151081231165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152179957438860278199799093 14266871009893151081231165)
      ·
        refine ⟨5350076628709931655461687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14266871009893151081231165 5350076628709931655461687)
        ·
          refine ⟨8025114943064897483192531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350076628709931655461687 8025114943064897483192531)
          ·
            refine ⟨12037672414597346224788797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025114943064897483192531 12037672414597346224788797)
            ·
              refine ⟨4514127155474004834295799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12037672414597346224788797 4514127155474004834295799)
              ·
                refine ⟨6771190733211007251443699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514127155474004834295799 6771190733211007251443699)
                ·
                  refine ⟨10156786099816510877165549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771190733211007251443699 10156786099816510877165549)
                  ·
                    refine ⟨3808794787431191578937081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10156786099816510877165549 3808794787431191578937081)
                    ·
                      refine ⟨2856596090573393684202811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808794787431191578937081 2856596090573393684202811)
                      ·
                        rfl

theorem cell23_5563201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5563201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563201 prefixEnd_5563201 := by exact prefixLift 5563201
  have htrace : WordTrace (prefixWord ++ tailWord_5563201) baseStart_5563201 baseEnd_5563201 := by
    simpa [prefixWord, tailWord_5563201, baseEnd_5563201] using wordTrace_append hprefix tailTrace_5563201
  have hstable : (prefixWord ++ tailWord_5563201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563201).length < 2 ^ (prefixWord ++ tailWord_5563201).sum := by decide
  have hdescent : baseEnd_5563201 < baseStart_5563201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563203 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 5]
def baseStart_5563203 : Nat := 118140960795 + 5563203 * 2 ^ 59
def prefixEnd_5563203 : Nat := 4983230072969 + 3 ^ 40 * 5563203 * 2
def baseEnd_5563203 : Nat := 317399679726078075153089

theorem tailTrace_5563203 : CollatzResearch.WordTrace tailWord_5563203 prefixEnd_5563203 317399679726078075153089 := by
  unfold tailWord_5563203
  simp only [CollatzResearch.WordTrace]
  refine ⟨202906682864473125274638263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135271121909648750183092175 202906682864473125274638263)
  ·
    refine ⟨304360024296709687911957395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202906682864473125274638263 304360024296709687911957395)
    ·
      refine ⟨456540036445064531867936093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304360024296709687911957395 456540036445064531867936093)
      ·
        refine ⟨171202513666899199450476035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456540036445064531867936093 171202513666899199450476035)
        ·
          refine ⟨256803770500348799175714053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171202513666899199450476035 256803770500348799175714053)
          ·
            refine ⟨48150706968815399845446385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256803770500348799175714053 48150706968815399845446385)
            ·
              refine ⟨36113030226611549884084789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48150706968815399845446385 36113030226611549884084789)
              ·
                refine ⟨3385596583744832801632949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36113030226611549884084789 3385596583744832801632949)
                ·
                  refine ⟨317399679726078075153089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3385596583744832801632949 317399679726078075153089)
                  ·
                    rfl

theorem cell23_5563203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 5].length) (baseStart_5563203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563203 prefixEnd_5563203 := by exact prefixLift 5563203
  have htrace : WordTrace (prefixWord ++ tailWord_5563203) baseStart_5563203 baseEnd_5563203 := by
    simpa [prefixWord, tailWord_5563203, baseEnd_5563203] using wordTrace_append hprefix tailTrace_5563203
  have hstable : (prefixWord ++ tailWord_5563203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563203).length < 2 ^ (prefixWord ++ tailWord_5563203).sum := by decide
  have hdescent : baseEnd_5563203 < baseStart_5563203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563256 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_5563256 : Nat := 118140960795 + 5563256 * 2 ^ 59
def prefixEnd_5563256 : Nat := 4983230072969 + 3 ^ 40 * 5563256 * 2
def baseEnd_5563256 : Nat := 2856624332009390969015057

theorem tailTrace_5563256 : CollatzResearch.WordTrace tailWord_5563256 prefixEnd_5563256 2856624332009390969015057 := by
  unfold tailWord_5563256
  simp only [CollatzResearch.WordTrace]
  refine ⟨101454307966640557663158811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135272410622187410217545081 101454307966640557663158811)
  ·
    refine ⟨152181461949960836494738217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101454307966640557663158811 152181461949960836494738217)
    ·
      refine ⟨114136096462470627371053663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152181461949960836494738217 114136096462470627371053663)
      ·
        refine ⟨171204144693705941056580495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114136096462470627371053663 171204144693705941056580495)
        ·
          refine ⟨256806217040558911584870743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171204144693705941056580495 256806217040558911584870743)
          ·
            refine ⟨385209325560838367377306115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256806217040558911584870743 385209325560838367377306115)
            ·
              refine ⟨577813988341257551065959173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385209325560838367377306115 577813988341257551065959173)
              ·
                refine ⟨108340122813985790824867345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577813988341257551065959173 108340122813985790824867345)
                ·
                  refine ⟨81255092110489343118650509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108340122813985790824867345 81255092110489343118650509)
                  ·
                    refine ⟨30470659541433503669493941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81255092110489343118650509 30470659541433503669493941)
                    ·
                      refine ⟨2856624332009390969015057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30470659541433503669493941 2856624332009390969015057)
                      ·
                        rfl

theorem cell23_5563256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_5563256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563256 prefixEnd_5563256 := by exact prefixLift 5563256
  have htrace : WordTrace (prefixWord ++ tailWord_5563256) baseStart_5563256 baseEnd_5563256 := by
    simpa [prefixWord, tailWord_5563256, baseEnd_5563256] using wordTrace_append hprefix tailTrace_5563256
  have hstable : (prefixWord ++ tailWord_5563256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563256).length < 2 ^ (prefixWord ++ tailWord_5563256).sum := by decide
  have hdescent : baseEnd_5563256 < baseStart_5563256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563357 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_5563357 : Nat := 118140960795 + 5563357 * 2 ^ 59
def prefixEnd_5563357 : Nat := 4983230072969 + 3 ^ 40 * 5563357 * 2
def baseEnd_5563357 : Nat := 952225397851831691284031

theorem tailTrace_5563357 : CollatzResearch.WordTrace tailWord_5563357 prefixEnd_5563357 952225397851831691284031 := by
  unfold tailWord_5563357
  simp only [CollatzResearch.WordTrace]
  refine ⟨202912299705915209575744325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135274866470610139717162883 202912299705915209575744325)
  ·
    refine ⟨38046056194859101795452061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202912299705915209575744325 38046056194859101795452061)
    ·
      refine ⟨14267271073072163173294523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38046056194859101795452061 14267271073072163173294523)
      ·
        refine ⟨21400906609608244759941785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14267271073072163173294523 21400906609608244759941785)
        ·
          refine ⟨16050679957206183569956339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21400906609608244759941785 16050679957206183569956339)
          ·
            refine ⟨24076019935809275354934509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16050679957206183569956339 24076019935809275354934509)
            ·
              refine ⟨9028507475928478258100441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24076019935809275354934509 9028507475928478258100441)
              ·
                refine ⟨6771380606946358693575331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9028507475928478258100441 6771380606946358693575331)
                ·
                  refine ⟨10157070910419538040362997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771380606946358693575331 10157070910419538040362997)
                  ·
                    refine ⟨952225397851831691284031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10157070910419538040362997 952225397851831691284031)
                    ·
                      rfl

theorem cell23_5563357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_5563357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563357 prefixEnd_5563357 := by exact prefixLift 5563357
  have htrace : WordTrace (prefixWord ++ tailWord_5563357) baseStart_5563357 baseEnd_5563357 := by
    simpa [prefixWord, tailWord_5563357, baseEnd_5563357] using wordTrace_append hprefix tailTrace_5563357
  have hstable : (prefixWord ++ tailWord_5563357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563357).length < 2 ^ (prefixWord ++ tailWord_5563357).sum := by decide
  have hdescent : baseEnd_5563357 < baseStart_5563357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563370 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_5563370 : Nat := 118140960795 + 5563370 * 2 ^ 59
def prefixEnd_5563370 : Nat := 4983230072969 + 3 ^ 40 * 5563370 * 2
def baseEnd_5563370 : Nat := 952227622934667840996511

theorem tailTrace_5563370 : CollatzResearch.WordTrace tailWord_5563370 prefixEnd_5563370 952227622934667840996511 := by
  unfold tailWord_5563370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50728193463717028198991891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135275182569912075197311709 50728193463717028198991891)
  ·
    refine ⟨76092290195575542298487837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50728193463717028198991891 76092290195575542298487837)
    ·
      refine ⟨28534608823340828361932939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76092290195575542298487837 28534608823340828361932939)
      ·
        refine ⟨42801913235011242542899409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28534608823340828361932939 42801913235011242542899409)
        ·
          refine ⟨32101434926258431907174557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42801913235011242542899409 32101434926258431907174557)
          ·
            refine ⟨12038038097346911965190459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32101434926258431907174557 12038038097346911965190459)
            ·
              refine ⟨18057057146020367947785689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12038038097346911965190459 18057057146020367947785689)
              ·
                refine ⟨13542792859515275960839267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18057057146020367947785689 13542792859515275960839267)
                ·
                  refine ⟨20314189289272913941258901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542792859515275960839267 20314189289272913941258901)
                  ·
                    refine ⟨952227622934667840996511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20314189289272913941258901 952227622934667840996511)
                    ·
                      rfl

theorem cell23_5563370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_5563370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563370 prefixEnd_5563370 := by exact prefixLift 5563370
  have htrace : WordTrace (prefixWord ++ tailWord_5563370) baseStart_5563370 baseEnd_5563370 := by
    simpa [prefixWord, tailWord_5563370, baseEnd_5563370] using wordTrace_append hprefix tailTrace_5563370
  have hstable : (prefixWord ++ tailWord_5563370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563370).length < 2 ^ (prefixWord ++ tailWord_5563370).sum := by decide
  have hdescent : baseEnd_5563370 < baseStart_5563370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563374 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5563374 : Nat := 118140960795 + 5563374 * 2 ^ 59
def prefixEnd_5563374 : Nat := 4983230072969 + 3 ^ 40 * 5563374 * 2
def baseEnd_5563374 : Nat := 952228307575540502446505

theorem tailTrace_5563374 : CollatzResearch.WordTrace tailWord_5563374 prefixEnd_5563374 952228307575540502446505 := by
  unfold tailWord_5563374
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364114968356702684889147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135275279831235747652742117 25364114968356702684889147)
  ·
    refine ⟨38046172452535054027333721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25364114968356702684889147 38046172452535054027333721)
    ·
      refine ⟨28534629339401290520500291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38046172452535054027333721 28534629339401290520500291)
      ·
        refine ⟨42801944009101935780750437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28534629339401290520500291 42801944009101935780750437)
        ·
          refine ⟨8025364501706612958890707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42801944009101935780750437 8025364501706612958890707)
          ·
            refine ⟨12038046752559919438336061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025364501706612958890707 12038046752559919438336061)
            ·
              refine ⟨4514267532209969789376023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12038046752559919438336061 4514267532209969789376023)
              ·
                refine ⟨6771401298314954684064035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514267532209969789376023 6771401298314954684064035)
                ·
                  refine ⟨10157101947472432026096053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771401298314954684064035 10157101947472432026096053)
                  ·
                    refine ⟨952228307575540502446505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10157101947472432026096053 952228307575540502446505)
                    ·
                      rfl

theorem cell23_5563374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5563374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563374 prefixEnd_5563374 := by exact prefixLift 5563374
  have htrace : WordTrace (prefixWord ++ tailWord_5563374) baseStart_5563374 baseEnd_5563374 := by
    simpa [prefixWord, tailWord_5563374, baseEnd_5563374] using wordTrace_append hprefix tailTrace_5563374
  have hstable : (prefixWord ++ tailWord_5563374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563374).length < 2 ^ (prefixWord ++ tailWord_5563374).sum := by decide
  have hdescent : baseEnd_5563374 < baseStart_5563374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563400 : List Nat := [2, 1, 3, 2, 1, 5, 1, 8]
def baseStart_5563400 : Nat := 118140960795 + 5563400 * 2 ^ 59
def prefixEnd_5563400 : Nat := 4983230072969 + 3 ^ 40 * 5563400 * 2
def baseEnd_5563400 : Nat := 105803639749023644652385

theorem tailTrace_5563400 : CollatzResearch.WordTrace tailWord_5563400 prefixEnd_5563400 105803639749023644652385 := by
  unfold tailWord_5563400
  simp only [CollatzResearch.WordTrace]
  refine ⟨101456934022379713959779827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135275912029839618613039769 101456934022379713959779827)
  ·
    refine ⟨152185401033569570939669741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101456934022379713959779827 152185401033569570939669741)
    ·
      refine ⟨57069525387588589102376153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152185401033569570939669741 57069525387588589102376153)
      ·
        refine ⟨42802144040691441826782115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57069525387588589102376153 42802144040691441826782115)
        ·
          refine ⟨64203216061037162740173173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42802144040691441826782115 64203216061037162740173173)
          ·
            refine ⟨6019051505722234006891235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64203216061037162740173173 6019051505722234006891235)
            ·
              refine ⟨9028577258583351010336853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019051505722234006891235 9028577258583351010336853)
              ·
                refine ⟨105803639749023644652385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9028577258583351010336853 105803639749023644652385)
                ·
                  rfl

theorem cell23_5563400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 8].length) (baseStart_5563400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563400 prefixEnd_5563400 := by exact prefixLift 5563400
  have htrace : WordTrace (prefixWord ++ tailWord_5563400) baseStart_5563400 baseEnd_5563400 := by
    simpa [prefixWord, tailWord_5563400, baseEnd_5563400] using wordTrace_append hprefix tailTrace_5563400
  have hstable : (prefixWord ++ tailWord_5563400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563400).length < 2 ^ (prefixWord ++ tailWord_5563400).sum := by decide
  have hdescent : baseEnd_5563400 < baseStart_5563400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563428 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5563428 : Nat := 118140960795 + 5563428 * 2 ^ 59
def prefixEnd_5563428 : Nat := 4983230072969 + 3 ^ 40 * 5563428 * 2
def baseEnd_5563428 : Nat := 2856712650681964296064267

theorem tailTrace_5563428 : CollatzResearch.WordTrace tailWord_5563428 prefixEnd_5563428 2856712650681964296064267 := by
  unfold tailWord_5563428
  simp only [CollatzResearch.WordTrace]
  refine ⟨101457444644328994350789469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135276592859105325801052625 101457444644328994350789469)
  ·
    refine ⟨38046541741623372881546051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101457444644328994350789469 38046541741623372881546051)
    ·
      refine ⟨57069812612435059322319077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046541741623372881546051 57069812612435059322319077)
      ·
        refine ⟨10700589864831573622934827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57069812612435059322319077 10700589864831573622934827)
        ·
          refine ⟨16050884797247360434402241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10700589864831573622934827 16050884797247360434402241)
          ·
            refine ⟨12038163597935520325801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16050884797247360434402241 12038163597935520325801681)
            ·
              refine ⟨9028622698451640244351261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12038163597935520325801681 9028622698451640244351261)
              ·
                refine ⟨3385733511919365091631723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9028622698451640244351261 3385733511919365091631723)
                ·
                  refine ⟨5078600267879047637447585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385733511919365091631723 5078600267879047637447585)
                  ·
                    refine ⟨3808950200909285728085689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078600267879047637447585 3808950200909285728085689)
                    ·
                      refine ⟨2856712650681964296064267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808950200909285728085689 2856712650681964296064267)
                      ·
                        rfl

theorem cell23_5563428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5563428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563428 prefixEnd_5563428 := by exact prefixLift 5563428
  have htrace : WordTrace (prefixWord ++ tailWord_5563428) baseStart_5563428 baseEnd_5563428 := by
    simpa [prefixWord, tailWord_5563428, baseEnd_5563428] using wordTrace_append hprefix tailTrace_5563428
  have hstable : (prefixWord ++ tailWord_5563428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563428).length < 2 ^ (prefixWord ++ tailWord_5563428).sum := by decide
  have hdescent : baseEnd_5563428 < baseStart_5563428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563431 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5563431 : Nat := 118140960795 + 5563431 * 2 ^ 59
def prefixEnd_5563431 : Nat := 4983230072969 + 3 ^ 40 * 5563431 * 2
def baseEnd_5563431 : Nat := 2856714191123927784326753

theorem tailTrace_5563431 : CollatzResearch.WordTrace tailWord_5563431 prefixEnd_5563431 2856714191123927784326753 := by
  unfold tailWord_5563431
  simp only [CollatzResearch.WordTrace]
  refine ⟨202914998707647120213938147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135276665805098080142625431 202914998707647120213938147)
  ·
    refine ⟨304372498061470680320907221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202914998707647120213938147 304372498061470680320907221)
    ·
      refine ⟨7133730423315719070021263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 304372498061470680320907221 7133730423315719070021263)
      ·
        refine ⟨10700595634973578605031895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133730423315719070021263 10700595634973578605031895)
        ·
          refine ⟨16050893452460367907547843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10700595634973578605031895 16050893452460367907547843)
          ·
            refine ⟨24076340178690551861321765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16050893452460367907547843 24076340178690551861321765)
            ·
              refine ⟨4514313783504478473997831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24076340178690551861321765 4514313783504478473997831)
              ·
                refine ⟨6771470675256717710996747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514313783504478473997831 6771470675256717710996747)
                ·
                  refine ⟨10157206012885076566495121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771470675256717710996747 10157206012885076566495121)
                  ·
                    refine ⟨7617904509663807424871341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157206012885076566495121 7617904509663807424871341)
                    ·
                      refine ⟨2856714191123927784326753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7617904509663807424871341 2856714191123927784326753)
                      ·
                        rfl

theorem cell23_5563431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5563431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563431 prefixEnd_5563431 := by exact prefixLift 5563431
  have htrace : WordTrace (prefixWord ++ tailWord_5563431) baseStart_5563431 baseEnd_5563431 := by
    simpa [prefixWord, tailWord_5563431, baseEnd_5563431] using wordTrace_append hprefix tailTrace_5563431
  have hstable : (prefixWord ++ tailWord_5563431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563431).length < 2 ^ (prefixWord ++ tailWord_5563431).sum := by decide
  have hdescent : baseEnd_5563431 < baseStart_5563431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563467 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 8, 2, 2]
def baseStart_5563467 : Nat := 118140960795 + 5563467 * 2 ^ 59
def prefixEnd_5563467 : Nat := 4983230072969 + 3 ^ 40 * 5563467 * 2
def baseEnd_5563467 : Nat := 2856732676427489643476587

theorem tailTrace_5563467 : CollatzResearch.WordTrace tailWord_5563467 prefixEnd_5563467 2856732676427489643476587 := by
  unfold tailWord_5563467
  simp only [CollatzResearch.WordTrace]
  refine ⟨202916311735516698362248655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135277541157011132241499103 202916311735516698362248655)
  ·
    refine ⟨304374467603275047543372983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202916311735516698362248655 304374467603275047543372983)
    ·
      refine ⟨456561701404912571315059475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304374467603275047543372983 456561701404912571315059475)
      ·
        refine ⟨684842552107368856972589213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456561701404912571315059475 684842552107368856972589213)
        ·
          refine ⟨256815957040263321364720955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684842552107368856972589213 256815957040263321364720955)
          ·
            refine ⟨385223935560394982047081433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256815957040263321364720955 385223935560394982047081433)
            ·
              refine ⟨288917951670296236535311075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385223935560394982047081433 288917951670296236535311075)
              ·
                refine ⟨433376927505444354802966613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288917951670296236535311075 433376927505444354802966613)
                ·
                  refine ⟨5078635869204426032847265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 433376927505444354802966613 5078635869204426032847265)
                  ·
                    refine ⟨3808976901903319524635449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078635869204426032847265 3808976901903319524635449)
                    ·
                      refine ⟨2856732676427489643476587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808976901903319524635449 2856732676427489643476587)
                      ·
                        rfl

theorem cell23_5563467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2, 2].length) (baseStart_5563467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563467 prefixEnd_5563467 := by exact prefixLift 5563467
  have htrace : WordTrace (prefixWord ++ tailWord_5563467) baseStart_5563467 baseEnd_5563467 := by
    simpa [prefixWord, tailWord_5563467, baseEnd_5563467] using wordTrace_append hprefix tailTrace_5563467
  have hstable : (prefixWord ++ tailWord_5563467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563467).length < 2 ^ (prefixWord ++ tailWord_5563467).sum := by decide
  have hdescent : baseEnd_5563467 < baseStart_5563467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563470 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5563470 : Nat := 118140960795 + 5563470 * 2 ^ 59
def prefixEnd_5563470 : Nat := 4983230072969 + 3 ^ 40 * 5563470 * 2
def baseEnd_5563470 : Nat := 2856734216869453131739073

theorem tailTrace_5563470 : CollatzResearch.WordTrace tailWord_5563470 prefixEnd_5563470 2856734216869453131739073 := by
  unfold tailWord_5563470
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364552644313228734325983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135277614103003886583071909 25364552644313228734325983)
  ·
    refine ⟨38046828966469843101488975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25364552644313228734325983 38046828966469843101488975)
    ·
      refine ⟨57070243449704764652233463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046828966469843101488975 57070243449704764652233463)
      ·
        refine ⟨85605365174557146978350195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57070243449704764652233463 85605365174557146978350195)
        ·
          refine ⟨128408047761835720467525293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85605365174557146978350195 128408047761835720467525293)
          ·
            refine ⟨48153017910688395175321985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128408047761835720467525293 48153017910688395175321985)
            ·
              refine ⟨36114763433016296381491489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48153017910688395175321985 36114763433016296381491489)
              ·
                refine ⟨27086072574762222286118617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36114763433016296381491489 27086072574762222286118617)
                ·
                  refine ⟨20314554431071666714588963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27086072574762222286118617 20314554431071666714588963)
                  ·
                    refine ⟨30471831646607500071883445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20314554431071666714588963 30471831646607500071883445)
                    ·
                      refine ⟨2856734216869453131739073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30471831646607500071883445 2856734216869453131739073)
                      ·
                        rfl

theorem cell23_5563470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5563470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563470 prefixEnd_5563470 := by exact prefixLift 5563470
  have htrace : WordTrace (prefixWord ++ tailWord_5563470) baseStart_5563470 baseEnd_5563470 := by
    simpa [prefixWord, tailWord_5563470, baseEnd_5563470] using wordTrace_append hprefix tailTrace_5563470
  have hstable : (prefixWord ++ tailWord_5563470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563470).length < 2 ^ (prefixWord ++ tailWord_5563470).sum := by decide
  have hdescent : baseEnd_5563470 < baseStart_5563470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563484 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5563484 : Nat := 118140960795 + 5563484 * 2 ^ 59
def prefixEnd_5563484 : Nat := 4983230072969 + 3 ^ 40 * 5563484 * 2
def baseEnd_5563484 : Nat := 2856741405598616076964009

theorem tailTrace_5563484 : CollatzResearch.WordTrace tailWord_5563484 prefixEnd_5563484 2856741405598616076964009 := by
  unfold tailWord_5563484
  simp only [CollatzResearch.WordTrace]
  refine ⟨101458465888227555132808753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135277954517636740177078337 101458465888227555132808753)
  ·
    refine ⟨76093849416170666349606565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101458465888227555132808753 76093849416170666349606565)
    ·
      refine ⟨14267596765531999940551231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76093849416170666349606565 14267596765531999940551231)
      ·
        refine ⟨21401395148297999910826847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14267596765531999940551231 21401395148297999910826847)
        ·
          refine ⟨32102092722446999866240271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21401395148297999910826847 32102092722446999866240271)
          ·
            refine ⟨48153139083670499799360407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32102092722446999866240271 48153139083670499799360407)
            ·
              refine ⟨72229708625505749699040611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48153139083670499799360407 72229708625505749699040611)
              ·
                refine ⟨108344562938258624548560917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72229708625505749699040611 108344562938258624548560917)
                ·
                  refine ⟨5078651387730873025713793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108344562938258624548560917 5078651387730873025713793)
                  ·
                    refine ⟨3808988540798154769285345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078651387730873025713793 3808988540798154769285345)
                    ·
                      refine ⟨2856741405598616076964009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3808988540798154769285345 2856741405598616076964009)
                      ·
                        rfl

theorem cell23_5563484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5563484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563484 prefixEnd_5563484 := by exact prefixLift 5563484
  have htrace : WordTrace (prefixWord ++ tailWord_5563484) baseStart_5563484 baseEnd_5563484 := by
    simpa [prefixWord, tailWord_5563484, baseEnd_5563484] using wordTrace_append hprefix tailTrace_5563484
  have hstable : (prefixWord ++ tailWord_5563484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563484).length < 2 ^ (prefixWord ++ tailWord_5563484).sum := by decide
  have hdescent : baseEnd_5563484 < baseStart_5563484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563530 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5563530 : Nat := 118140960795 + 5563530 * 2 ^ 59
def prefixEnd_5563530 : Nat := 4983230072969 + 3 ^ 40 * 5563530 * 2
def baseEnd_5563530 : Nat := 2856765025708722896988797

theorem tailTrace_5563530 : CollatzResearch.WordTrace tailWord_5563530 prefixEnd_5563530 2856765025708722896988797 := by
  unfold tailWord_5563530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729652383572115030448011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135279073022858973414528029 50729652383572115030448011)
  ·
    refine ⟨76094478575358172545672017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50729652383572115030448011 76094478575358172545672017)
    ·
      refine ⟨57070858931518629409254013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76094478575358172545672017 57070858931518629409254013)
      ·
        refine ⟨21401572099319486028470255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57070858931518629409254013 21401572099319486028470255)
        ·
          refine ⟨32102358148979229042705383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21401572099319486028470255 32102358148979229042705383)
          ·
            refine ⟨48153537223468843564058075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32102358148979229042705383 48153537223468843564058075)
            ·
              refine ⟨72230305835203265346087113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48153537223468843564058075 72230305835203265346087113)
              ·
                refine ⟨54172729376402449009565335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72230305835203265346087113 54172729376402449009565335)
                ·
                  refine ⟨81259094064603673514348003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54172729376402449009565335 81259094064603673514348003)
                  ·
                    refine ⟨121888641096905510271522005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81259094064603673514348003 121888641096905510271522005)
                    ·
                      refine ⟨2856765025708722896988797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121888641096905510271522005 2856765025708722896988797)
                      ·
                        rfl

theorem cell23_5563530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5563530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563530 prefixEnd_5563530 := by exact prefixLift 5563530
  have htrace : WordTrace (prefixWord ++ tailWord_5563530) baseStart_5563530 baseEnd_5563530 := by
    simpa [prefixWord, tailWord_5563530, baseEnd_5563530] using wordTrace_append hprefix tailTrace_5563530
  have hstable : (prefixWord ++ tailWord_5563530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563530).length < 2 ^ (prefixWord ++ tailWord_5563530).sum := by decide
  have hdescent : baseEnd_5563530 < baseStart_5563530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563557 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_5563557 : Nat := 118140960795 + 5563557 * 2 ^ 59
def prefixEnd_5563557 : Nat := 4983230072969 + 3 ^ 40 * 5563557 * 2
def baseEnd_5563557 : Nat := 2856778889686394291351173

theorem tailTrace_5563557 : CollatzResearch.WordTrace tailWord_5563557 prefixEnd_5563557 2856778889686394291351173 := by
  unfold tailWord_5563557
  simp only [CollatzResearch.WordTrace]
  refine ⟨202919594305190643733024925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135279729536793762488683283 202919594305190643733024925)
  ·
    refine ⟨76094847864446491399884347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202919594305190643733024925 76094847864446491399884347)
    ·
      refine ⟨114142271796669737099826521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76094847864446491399884347 114142271796669737099826521)
      ·
        refine ⟨85606703847502302824869891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114142271796669737099826521 85606703847502302824869891)
        ·
          refine ⟨128410055771253454237304837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85606703847502302824869891 128410055771253454237304837)
          ·
            refine ⟨24076885457110022669494657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128410055771253454237304837 24076885457110022669494657)
            ·
              refine ⟨18057664092832517002120993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24076885457110022669494657 18057664092832517002120993)
              ·
                refine ⟨13543248069624387751590745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18057664092832517002120993 13543248069624387751590745)
                ·
                  refine ⟨10157436052218290813693059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13543248069624387751590745 10157436052218290813693059)
                  ·
                    refine ⟨15236154078327436220539589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10157436052218290813693059 15236154078327436220539589)
                    ·
                      refine ⟨2856778889686394291351173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15236154078327436220539589 2856778889686394291351173)
                      ·
                        rfl

theorem cell23_5563557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_5563557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563557 prefixEnd_5563557 := by exact prefixLift 5563557
  have htrace : WordTrace (prefixWord ++ tailWord_5563557) baseStart_5563557 baseEnd_5563557 := by
    simpa [prefixWord, tailWord_5563557, baseEnd_5563557] using wordTrace_append hprefix tailTrace_5563557
  have hstable : (prefixWord ++ tailWord_5563557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563557).length < 2 ^ (prefixWord ++ tailWord_5563557).sum := by decide
  have hdescent : baseEnd_5563557 < baseStart_5563557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563584 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_5563584 : Nat := 118140960795 + 5563584 * 2 ^ 59
def prefixEnd_5563584 : Nat := 4983230072969 + 3 ^ 40 * 5563584 * 2
def baseEnd_5563584 : Nat := 952264251221355228571183

theorem tailTrace_5563584 : CollatzResearch.WordTrace tailWord_5563584 prefixEnd_5563584 952264251221355228571183 := by
  unfold tailWord_5563584
  simp only [CollatzResearch.WordTrace]
  refine ⟨101460289538046413672128903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135280386050728551562838537 101460289538046413672128903)
  ·
    refine ⟨152190434307069620508193355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101460289538046413672128903 152190434307069620508193355)
    ·
      refine ⟨228285651460604430762290033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152190434307069620508193355 228285651460604430762290033)
      ·
        refine ⟨171214238595453323071717525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228285651460604430762290033 171214238595453323071717525)
        ·
          refine ⟨8025667434161874518986759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171214238595453323071717525 8025667434161874518986759)
          ·
            refine ⟨12038501151242811778480139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025667434161874518986759 12038501151242811778480139)
            ·
              refine ⟨18057751726864217667720209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12038501151242811778480139 18057751726864217667720209)
              ·
                refine ⟨13543313795148163250790157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18057751726864217667720209 13543313795148163250790157)
                ·
                  refine ⟨5078742673180561219046309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13543313795148163250790157 5078742673180561219046309)
                  ·
                    refine ⟨952264251221355228571183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078742673180561219046309 952264251221355228571183)
                    ·
                      rfl

theorem cell23_5563584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_5563584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563584 prefixEnd_5563584 := by exact prefixLift 5563584
  have htrace : WordTrace (prefixWord ++ tailWord_5563584) baseStart_5563584 baseEnd_5563584 := by
    simpa [prefixWord, tailWord_5563584, baseEnd_5563584] using wordTrace_append hprefix tailTrace_5563584
  have hstable : (prefixWord ++ tailWord_5563584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563584).length < 2 ^ (prefixWord ++ tailWord_5563584).sum := by decide
  have hdescent : baseEnd_5563584 < baseStart_5563584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563594 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_5563594 : Nat := 118140960795 + 5563594 * 2 ^ 59
def prefixEnd_5563594 : Nat := 4983230072969 + 3 ^ 40 * 5563594 * 2
def baseEnd_5563594 : Nat := 2856797888470610646588503

theorem tailTrace_5563594 : CollatzResearch.WordTrace tailWord_5563594 prefixEnd_5563594 2856797888470610646588503 := by
  unfold tailWord_5563594
  simp only [CollatzResearch.WordTrace]
  refine ⟨50730235951514149763030459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135280629204037732701414557 50730235951514149763030459)
  ·
    refine ⟨76095353927271224644545689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50730235951514149763030459 76095353927271224644545689)
    ·
      refine ⟨57071515445453418483409267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76095353927271224644545689 57071515445453418483409267)
      ·
        refine ⟨85607273168180127725113901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57071515445453418483409267 85607273168180127725113901)
        ·
          refine ⟨32102727438067547896917713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85607273168180127725113901 32102727438067547896917713)
          ·
            refine ⟨24077045578550660922688285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32102727438067547896917713 24077045578550660922688285)
            ·
              refine ⟨9028892091956497846008107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24077045578550660922688285 9028892091956497846008107)
              ·
                refine ⟨13543338137934746769012161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028892091956497846008107 13543338137934746769012161)
                ·
                  refine ⟨10157503603451060076759121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13543338137934746769012161 10157503603451060076759121)
                  ·
                    refine ⟨7618127702588295057569341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157503603451060076759121 7618127702588295057569341)
                    ·
                      refine ⟨2856797888470610646588503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618127702588295057569341 2856797888470610646588503)
                      ·
                        rfl

theorem cell23_5563594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_5563594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563594 prefixEnd_5563594 := by exact prefixLift 5563594
  have htrace : WordTrace (prefixWord ++ tailWord_5563594) baseStart_5563594 baseEnd_5563594 := by
    simpa [prefixWord, tailWord_5563594, baseEnd_5563594] using wordTrace_append hprefix tailTrace_5563594
  have hstable : (prefixWord ++ tailWord_5563594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563594).length < 2 ^ (prefixWord ++ tailWord_5563594).sum := by decide
  have hdescent : baseEnd_5563594 < baseStart_5563594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563657 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_5563657 : Nat := 118140960795 + 5563657 * 2 ^ 59
def prefixEnd_5563657 : Nat := 4983230072969 + 3 ^ 40 * 5563657 * 2
def baseEnd_5563657 : Nat := 952276745917281300033571

theorem tailTrace_5563657 : CollatzResearch.WordTrace tailWord_5563657 prefixEnd_5563657 952276745917281300033571 := by
  unfold tailWord_5563657
  simp only [CollatzResearch.WordTrace]
  refine ⟨202923241604828360811665225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135282161069885573874443483 202923241604828360811665225)
  ·
    refine ⟨152192431203621270608748919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202923241604828360811665225 152192431203621270608748919)
    ·
      refine ⟨228288646805431905913123379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152192431203621270608748919 228288646805431905913123379)
      ·
        refine ⟨342432970208147858869685069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228288646805431905913123379 342432970208147858869685069)
        ·
          refine ⟨128412363828055447076131901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342432970208147858869685069 128412363828055447076131901)
          ·
            refine ⟨48154636435520792653549463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128412363828055447076131901 48154636435520792653549463)
            ·
              refine ⟨72231954653281188980324195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48154636435520792653549463 72231954653281188980324195)
              ·
                refine ⟨108347931979921783470486293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72231954653281188980324195 108347931979921783470486293)
                ·
                  refine ⟨5078809311558833600179045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108347931979921783470486293 5078809311558833600179045)
                  ·
                    refine ⟨952276745917281300033571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078809311558833600179045 952276745917281300033571)
                    ·
                      rfl

theorem cell23_5563657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_5563657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563657 prefixEnd_5563657 := by exact prefixLift 5563657
  have htrace : WordTrace (prefixWord ++ tailWord_5563657) baseStart_5563657 baseEnd_5563657 := by
    simpa [prefixWord, tailWord_5563657, baseEnd_5563657] using wordTrace_append hprefix tailTrace_5563657
  have hstable : (prefixWord ++ tailWord_5563657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563657).length < 2 ^ (prefixWord ++ tailWord_5563657).sum := by decide
  have hdescent : baseEnd_5563657 < baseStart_5563657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563667 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3]
def baseStart_5563667 : Nat := 118140960795 + 5563667 * 2 ^ 59
def prefixEnd_5563667 : Nat := 4983230072969 + 3 ^ 40 * 5563667 * 2
def baseEnd_5563667 : Nat := 2856835372558388860975667

theorem tailTrace_5563667 : CollatzResearch.WordTrace tailWord_5563667 prefixEnd_5563667 2856835372558388860975667 := by
  unfold tailWord_5563667
  simp only [CollatzResearch.WordTrace]
  refine ⟨202923606334792132519529255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135282404223194755013019503 202923606334792132519529255)
  ·
    refine ⟨304385409502188198779293883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202923606334792132519529255 304385409502188198779293883)
    ·
      refine ⟨456578114253282298168940825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304385409502188198779293883 456578114253282298168940825)
      ·
        refine ⟨342433585689961723626705619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456578114253282298168940825 342433585689961723626705619)
        ·
          refine ⟨513650378534942585440058429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342433585689961723626705619 513650378534942585440058429)
          ·
            refine ⟨192618891950603469540021911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513650378534942585440058429 192618891950603469540021911)
            ·
              refine ⟨288928337925905204310032867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192618891950603469540021911 288928337925905204310032867)
              ·
                refine ⟨433392506888857806465049301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288928337925905204310032867 433392506888857806465049301)
                ·
                  refine ⟨10157636880207604839024593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 433392506888857806465049301 10157636880207604839024593)
                  ·
                    refine ⟨7618227660155703629268445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157636880207604839024593 7618227660155703629268445)
                    ·
                      refine ⟨2856835372558388860975667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618227660155703629268445 2856835372558388860975667)
                      ·
                        rfl

theorem cell23_5563667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_5563667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563667 prefixEnd_5563667 := by exact prefixLift 5563667
  have htrace : WordTrace (prefixWord ++ tailWord_5563667) baseStart_5563667 baseEnd_5563667 := by
    simpa [prefixWord, tailWord_5563667, baseEnd_5563667] using wordTrace_append hprefix tailTrace_5563667
  have hstable : (prefixWord ++ tailWord_5563667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563667).length < 2 ^ (prefixWord ++ tailWord_5563667).sum := by decide
  have hdescent : baseEnd_5563667 < baseStart_5563667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563674 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_5563674 : Nat := 118140960795 + 5563674 * 2 ^ 59
def prefixEnd_5563674 : Nat := 4983230072969 + 3 ^ 40 * 5563674 * 2
def baseEnd_5563674 : Nat := 952279655640990111196045

theorem tailTrace_5563674 : CollatzResearch.WordTrace tailWord_5563674 prefixEnd_5563674 952279655640990111196045 := by
  unfold tailWord_5563674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50730965411441693178758519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135282574430511181810022717 50730965411441693178758519)
  ·
    refine ⟨76096448117162539768137779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50730965411441693178758519 76096448117162539768137779)
    ·
      refine ⟨114144672175743809652206669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76096448117162539768137779 114144672175743809652206669)
      ·
        refine ⟨42804252065903928619577501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114144672175743809652206669 42804252065903928619577501)
        ·
          refine ⟨16051594524713973232341563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42804252065903928619577501 16051594524713973232341563)
          ·
            refine ⟨24077391787070959848512345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16051594524713973232341563 24077391787070959848512345)
            ·
              refine ⟨18058043840303219886384259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24077391787070959848512345 18058043840303219886384259)
              ·
                refine ⟨27087065760454829829576389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18058043840303219886384259 27087065760454829829576389)
                ·
                  refine ⟨5078824830085280593045573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27087065760454829829576389 5078824830085280593045573)
                  ·
                    refine ⟨952279655640990111196045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078824830085280593045573 952279655640990111196045)
                    ·
                      rfl

theorem cell23_5563674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_5563674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563674 prefixEnd_5563674 := by exact prefixLift 5563674
  have htrace : WordTrace (prefixWord ++ tailWord_5563674) baseStart_5563674 baseEnd_5563674 := by
    simpa [prefixWord, tailWord_5563674, baseEnd_5563674] using wordTrace_append hprefix tailTrace_5563674
  have hstable : (prefixWord ++ tailWord_5563674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563674).length < 2 ^ (prefixWord ++ tailWord_5563674).sum := by decide
  have hdescent : baseEnd_5563674 < baseStart_5563674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563684 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_5563684 : Nat := 118140960795 + 5563684 * 2 ^ 59
def prefixEnd_5563684 : Nat := 4983230072969 + 3 ^ 40 * 5563684 * 2
def baseEnd_5563684 : Nat := 2856844101729515294463089

theorem tailTrace_5563684 : CollatzResearch.WordTrace tailWord_5563684 prefixEnd_5563684 2856844101729515294463089 := by
  unfold tailWord_5563684
  simp only [CollatzResearch.WordTrace]
  refine ⟨101462113187865272211449053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135282817583820362948598737 101462113187865272211449053)
  ·
    refine ⟨38048292445449477079293395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101462113187865272211449053 38048292445449477079293395)
    ·
      refine ⟨57072438668174215618940093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38048292445449477079293395 57072438668174215618940093)
      ·
        refine ⟨21402164500565330857102535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57072438668174215618940093 21402164500565330857102535)
        ·
          refine ⟨32103246750847996285653803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21402164500565330857102535 32103246750847996285653803)
          ·
            refine ⟨48154870126271994428480705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32103246750847996285653803 48154870126271994428480705)
            ·
              refine ⟨36116152594703995821360529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48154870126271994428480705 36116152594703995821360529)
              ·
                refine ⟨27087114446027996866020397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36116152594703995821360529 27087114446027996866020397)
                ·
                  refine ⟨10157667917260498824757649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27087114446027996866020397 10157667917260498824757649)
                  ·
                    refine ⟨7618250937945374118568237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157667917260498824757649 7618250937945374118568237)
                    ·
                      refine ⟨2856844101729515294463089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618250937945374118568237 2856844101729515294463089)
                      ·
                        rfl

theorem cell23_5563684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_5563684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563684 prefixEnd_5563684 := by exact prefixLift 5563684
  have htrace : WordTrace (prefixWord ++ tailWord_5563684) baseStart_5563684 baseEnd_5563684 := by
    simpa [prefixWord, tailWord_5563684, baseEnd_5563684] using wordTrace_append hprefix tailTrace_5563684
  have hstable : (prefixWord ++ tailWord_5563684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563684).length < 2 ^ (prefixWord ++ tailWord_5563684).sum := by decide
  have hdescent : baseEnd_5563684 < baseStart_5563684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563701 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5563701 : Nat := 118140960795 + 5563701 * 2 ^ 59
def prefixEnd_5563701 : Nat := 4983230072969 + 3 ^ 40 * 5563701 * 2
def baseEnd_5563701 : Nat := 2856852830900641727950511

theorem tailTrace_5563701 : CollatzResearch.WordTrace tailWord_5563701 prefixEnd_5563701 2856852830900641727950511 := by
  unfold tailWord_5563701
  simp only [CollatzResearch.WordTrace]
  refine ⟨202924846416668956326266957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135283230944445970884177971 202924846416668956326266957)
  ·
    refine ⟨76096817406250858622350109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202924846416668956326266957 76096817406250858622350109)
    ·
      refine ⟨28536306527344071983381291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76096817406250858622350109 28536306527344071983381291)
      ·
        refine ⟨42804459791016107975071937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28536306527344071983381291 42804459791016107975071937)
        ·
          refine ⟨32103344843262080981303953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42804459791016107975071937 32103344843262080981303953)
          ·
            refine ⟨24077508632446560735977965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32103344843262080981303953 24077508632446560735977965)
            ·
              refine ⟨9029065737167460275991737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24077508632446560735977965 9029065737167460275991737)
              ·
                refine ⟨6771799302875595206993803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9029065737167460275991737 6771799302875595206993803)
                ·
                  refine ⟨10157698954313392810490705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771799302875595206993803 10157698954313392810490705)
                  ·
                    refine ⟨7618274215735044607868029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157698954313392810490705 7618274215735044607868029)
                    ·
                      refine ⟨2856852830900641727950511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618274215735044607868029 2856852830900641727950511)
                      ·
                        rfl

theorem cell23_5563701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5563701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563701 prefixEnd_5563701 := by exact prefixLift 5563701
  have htrace : WordTrace (prefixWord ++ tailWord_5563701) baseStart_5563701 baseEnd_5563701 := by
    simpa [prefixWord, tailWord_5563701, baseEnd_5563701] using wordTrace_append hprefix tailTrace_5563701
  have hstable : (prefixWord ++ tailWord_5563701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563701).length < 2 ^ (prefixWord ++ tailWord_5563701).sum := by decide
  have hdescent : baseEnd_5563701 < baseStart_5563701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563725 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5563725 : Nat := 118140960795 + 5563725 * 2 ^ 59
def prefixEnd_5563725 : Nat := 4983230072969 + 3 ^ 40 * 5563725 * 2
def baseEnd_5563725 : Nat := 952288384812116544683467

theorem tailTrace_5563725 : CollatzResearch.WordTrace tailWord_5563725 prefixEnd_5563725 952288384812116544683467 := by
  unfold tailWord_5563725
  simp only [CollatzResearch.WordTrace]
  refine ⟨202925721768582008425140629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135283814512388005616760419 202925721768582008425140629)
  ·
    refine ⟨9512143207902281644928467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202925721768582008425140629 9512143207902281644928467)
    ·
      refine ⟨14268214811853422467392701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9512143207902281644928467 14268214811853422467392701)
      ·
        refine ⟨5350580554445033425272263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14268214811853422467392701 5350580554445033425272263)
        ·
          refine ⟨8025870831667550137908395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350580554445033425272263 8025870831667550137908395)
          ·
            refine ⟨12038806247501325206862593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025870831667550137908395 12038806247501325206862593)
            ·
              refine ⟨9029104685625993905146945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12038806247501325206862593 9029104685625993905146945)
              ·
                refine ⟨6771828514219495428860209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9029104685625993905146945 6771828514219495428860209)
                ·
                  refine ⟨5078871385664621571645157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6771828514219495428860209 5078871385664621571645157)
                  ·
                    refine ⟨952288384812116544683467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078871385664621571645157 952288384812116544683467)
                    ·
                      rfl

theorem cell23_5563725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5563725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563725 prefixEnd_5563725 := by exact prefixLift 5563725
  have htrace : WordTrace (prefixWord ++ tailWord_5563725) baseStart_5563725 baseEnd_5563725 := by
    simpa [prefixWord, tailWord_5563725, baseEnd_5563725] using wordTrace_append hprefix tailTrace_5563725
  have hstable : (prefixWord ++ tailWord_5563725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563725).length < 2 ^ (prefixWord ++ tailWord_5563725).sum := by decide
  have hdescent : baseEnd_5563725 < baseStart_5563725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563731 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 3]
def baseStart_5563731 : Nat := 118140960795 + 5563731 * 2 ^ 59
def prefixEnd_5563731 : Nat := 4983230072969 + 3 ^ 40 * 5563731 * 2
def baseEnd_5563731 : Nat := 2856868235320276610575373

theorem tailTrace_5563731 : CollatzResearch.WordTrace tailWord_5563731 prefixEnd_5563731 2856868235320276610575373 := by
  unfold tailWord_5563731
  simp only [CollatzResearch.WordTrace]
  refine ⟨202925940606560271449859047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135283960404373514299906031 202925940606560271449859047)
  ·
    refine ⟨304388910909840407174788571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202925940606560271449859047 304388910909840407174788571)
    ·
      refine ⟨456583366364760610762182857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304388910909840407174788571 456583366364760610762182857)
      ·
        refine ⟨342437524773570458071637143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456583366364760610762182857 342437524773570458071637143)
        ·
          refine ⟨513656287160355687107455715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342437524773570458071637143 513656287160355687107455715)
          ·
            refine ⟨770484430740533530661183573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513656287160355687107455715 770484430740533530661183573)
            ·
              refine ⟨9029114422740627312435745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 770484430740533530661183573 9029114422740627312435745)
              ·
                refine ⟨6771835817055470484326809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9029114422740627312435745 6771835817055470484326809)
                ·
                  refine ⟨5078876862791602863245107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6771835817055470484326809 5078876862791602863245107)
                  ·
                    refine ⟨7618315294187404294867661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5078876862791602863245107 7618315294187404294867661)
                    ·
                      refine ⟨2856868235320276610575373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618315294187404294867661 2856868235320276610575373)
                      ·
                        rfl

theorem cell23_5563731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_5563731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563731 prefixEnd_5563731 := by exact prefixLift 5563731
  have htrace : WordTrace (prefixWord ++ tailWord_5563731) baseStart_5563731 baseEnd_5563731 := by
    simpa [prefixWord, tailWord_5563731, baseEnd_5563731] using wordTrace_append hprefix tailTrace_5563731
  have hstable : (prefixWord ++ tailWord_5563731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563731).length < 2 ^ (prefixWord ++ tailWord_5563731).sum := by decide
  have hdescent : baseEnd_5563731 < baseStart_5563731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563737 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_5563737 : Nat := 118140960795 + 5563737 * 2 ^ 59
def prefixEnd_5563737 : Nat := 4983230072969 + 3 ^ 40 * 5563737 * 2
def baseEnd_5563737 : Nat := 2856871316204203587100345

theorem tailTrace_5563737 : CollatzResearch.WordTrace tailWord_5563737 prefixEnd_5563737 2856871316204203587100345 := by
  unfold tailWord_5563737
  simp only [CollatzResearch.WordTrace]
  refine ⟨202926159444538534474577465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135284106296359022983051643 202926159444538534474577465)
  ·
    refine ⟨152194619583403900855933099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202926159444538534474577465 152194619583403900855933099)
    ·
      refine ⟨228291929375105851283899649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152194619583403900855933099 228291929375105851283899649)
      ·
        refine ⟨171218947031329388462924737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228291929375105851283899649 171218947031329388462924737)
        ·
          refine ⟨128414210273497041347193553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171218947031329388462924737 128414210273497041347193553)
          ·
            refine ⟨96310657705122781010395165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128414210273497041347193553 96310657705122781010395165)
            ·
              refine ⟨36116496639421042878898187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96310657705122781010395165 36116496639421042878898187)
              ·
                refine ⟨54174744959131564318347281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36116496639421042878898187 54174744959131564318347281)
                ·
                  refine ⟨40631058719348673238760461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54174744959131564318347281 40631058719348673238760461)
                  ·
                    refine ⟨15236647019755752464535173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40631058719348673238760461 15236647019755752464535173)
                    ·
                      refine ⟨2856871316204203587100345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15236647019755752464535173 2856871316204203587100345)
                      ·
                        rfl

theorem cell23_5563737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_5563737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563737 prefixEnd_5563737 := by exact prefixLift 5563737
  have htrace : WordTrace (prefixWord ++ tailWord_5563737) baseStart_5563737 baseEnd_5563737 := by
    simpa [prefixWord, tailWord_5563737, baseEnd_5563737] using wordTrace_append hprefix tailTrace_5563737
  have hstable : (prefixWord ++ tailWord_5563737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563737).length < 2 ^ (prefixWord ++ tailWord_5563737).sum := by decide
  have hdescent : baseEnd_5563737 < baseStart_5563737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563747 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 8]
def baseStart_5563747 : Nat := 118140960795 + 5563747 * 2 ^ 59
def prefixEnd_5563747 : Nat := 4983230072969 + 3 ^ 40 * 5563747 * 2
def baseEnd_5563747 : Nat := 952292150336916182658433

theorem tailTrace_5563747 : CollatzResearch.WordTrace tailWord_5563747 prefixEnd_5563747 952292150336916182658433 := by
  unfold tailWord_5563747
  simp only [CollatzResearch.WordTrace]
  refine ⟨202926524174502306182441495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135284349449668204121627663 202926524174502306182441495)
  ·
    refine ⟨304389786261753459273662243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202926524174502306182441495 304389786261753459273662243)
    ·
      refine ⟨456584679392630188910493365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304389786261753459273662243 456584679392630188910493365)
      ·
        refine ⟨42804813693059080210358753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 456584679392630188910493365 42804813693059080210358753)
        ·
          refine ⟨32103610269794310157769065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42804813693059080210358753 32103610269794310157769065)
          ·
            refine ⟨24077707702345732618326799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32103610269794310157769065 24077707702345732618326799)
            ·
              refine ⟨36116561553518598927490199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24077707702345732618326799 36116561553518598927490199)
              ·
                refine ⟨54174842330277898391235299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36116561553518598927490199 54174842330277898391235299)
                ·
                  refine ⟨81262263495416847586852949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54174842330277898391235299 81262263495416847586852949)
                  ·
                    refine ⟨952292150336916182658433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81262263495416847586852949 952292150336916182658433)
                    ·
                      rfl

theorem cell23_5563747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_5563747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563747 prefixEnd_5563747 := by exact prefixLift 5563747
  have htrace : WordTrace (prefixWord ++ tailWord_5563747) baseStart_5563747 baseEnd_5563747 := by
    simpa [prefixWord, tailWord_5563747, baseEnd_5563747] using wordTrace_append hprefix tailTrace_5563747
  have hstable : (prefixWord ++ tailWord_5563747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563747).length < 2 ^ (prefixWord ++ tailWord_5563747).sum := by decide
  have hdescent : baseEnd_5563747 < baseStart_5563747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563767 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_5563767 : Nat := 118140960795 + 5563767 * 2 ^ 59
def prefixEnd_5563767 : Nat := 4983230072969 + 3 ^ 40 * 5563767 * 2
def baseEnd_5563767 : Nat := 2856886720623838469725207

theorem tailTrace_5563767 : CollatzResearch.WordTrace tailWord_5563767 prefixEnd_5563767 2856886720623838469725207 := by
  unfold tailWord_5563767
  simp only [CollatzResearch.WordTrace]
  refine ⟨202927253634429849598169555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135284835756286566398779703 202927253634429849598169555)
  ·
    refine ⟨304390880451644774397254333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202927253634429849598169555 304390880451644774397254333)
    ·
      refine ⟨114146580169366790398970375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304390880451644774397254333 114146580169366790398970375)
      ·
        refine ⟨171219870254050185598455563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114146580169366790398970375 171219870254050185598455563)
        ·
          refine ⟨256829805381075278397683345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171219870254050185598455563 256829805381075278397683345)
          ·
            refine ⟨192622354035806458798262509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256829805381075278397683345 192622354035806458798262509)
            ·
              refine ⟨72233382763427422049348441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192622354035806458798262509 72233382763427422049348441)
              ·
                refine ⟨54175037072570566537011331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72233382763427422049348441 54175037072570566537011331)
                ·
                  refine ⟨81262555608855849805516997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54175037072570566537011331 81262555608855849805516997)
                  ·
                    refine ⟨15236729176660471838534437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81262555608855849805516997 15236729176660471838534437)
                    ·
                      refine ⟨2856886720623838469725207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15236729176660471838534437 2856886720623838469725207)
                      ·
                        rfl

theorem cell23_5563767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_5563767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563767 prefixEnd_5563767 := by exact prefixLift 5563767
  have htrace : WordTrace (prefixWord ++ tailWord_5563767) baseStart_5563767 baseEnd_5563767 := by
    simpa [prefixWord, tailWord_5563767, baseEnd_5563767] using wordTrace_append hprefix tailTrace_5563767
  have hstable : (prefixWord ++ tailWord_5563767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563767).length < 2 ^ (prefixWord ++ tailWord_5563767).sum := by decide
  have hdescent : baseEnd_5563767 < baseStart_5563767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563771 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 4, 2, 2]
def baseStart_5563771 : Nat := 118140960795 + 5563771 * 2 ^ 59
def prefixEnd_5563771 : Nat := 4983230072969 + 3 ^ 40 * 5563771 * 2
def baseEnd_5563771 : Nat := 2856888774546456454075189

theorem tailTrace_5563771 : CollatzResearch.WordTrace tailWord_5563771 prefixEnd_5563771 2856888774546456454075189 := by
  unfold tailWord_5563771
  simp only [CollatzResearch.WordTrace]
  refine ⟨202927399526415358281315167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135284933017610238854210111 202927399526415358281315167)
  ·
    refine ⟨304391099289623037421972751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202927399526415358281315167 304391099289623037421972751)
    ·
      refine ⟨456586648934434556132959127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304391099289623037421972751 456586648934434556132959127)
      ·
        refine ⟨684879973401651834199438691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456586648934434556132959127 684879973401651834199438691)
        ·
          refine ⟨1027319960102477751299158037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684879973401651834199438691 1027319960102477751299158037)
          ·
            refine ⟨48155623129803644592148033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1027319960102477751299158037 48155623129803644592148033)
            ·
              refine ⟨36116717347352733444111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48155623129803644592148033 36116717347352733444111025)
              ·
                refine ⟨27087538010514550083083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36116717347352733444111025 27087538010514550083083269)
                ·
                  refine ⟨5078913376971478140578113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27087538010514550083083269 5078913376971478140578113)
                  ·
                    refine ⟨3809185032728608605433585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078913376971478140578113 3809185032728608605433585)
                    ·
                      refine ⟨2856888774546456454075189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809185032728608605433585 2856888774546456454075189)
                      ·
                        rfl

theorem cell23_5563771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2, 2].length) (baseStart_5563771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563771 prefixEnd_5563771 := by exact prefixLift 5563771
  have htrace : WordTrace (prefixWord ++ tailWord_5563771) baseStart_5563771 baseEnd_5563771 := by
    simpa [prefixWord, tailWord_5563771, baseEnd_5563771] using wordTrace_append hprefix tailTrace_5563771
  have hstable : (prefixWord ++ tailWord_5563771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563771).length < 2 ^ (prefixWord ++ tailWord_5563771).sum := by decide
  have hdescent : baseEnd_5563771 < baseStart_5563771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563784 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5563784 : Nat := 118140960795 + 5563784 * 2 ^ 59
def prefixEnd_5563784 : Nat := 4983230072969 + 3 ^ 40 * 5563784 * 2
def baseEnd_5563784 : Nat := 2856895449794964903212629

theorem tailTrace_5563784 : CollatzResearch.WordTrace tailWord_5563784 prefixEnd_5563784 2856895449794964903212629 := by
  unfold tailWord_5563784
  simp only [CollatzResearch.WordTrace]
  refine ⟨101463936837684130750769203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135285249116912174334358937 101463936837684130750769203)
  ·
    refine ⟨152195905256526196126153805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101463936837684130750769203 152195905256526196126153805)
    ·
      refine ⟨57073464471197323547307677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152195905256526196126153805 57073464471197323547307677)
      ·
        refine ⟨21402549176698996330240379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57073464471197323547307677 21402549176698996330240379)
        ·
          refine ⟨32103823765048494495360569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21402549176698996330240379 32103823765048494495360569)
          ·
            refine ⟨24077867823786370871520427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32103823765048494495360569 24077867823786370871520427)
            ·
              refine ⟨36116801735679556307280641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24077867823786370871520427 36116801735679556307280641)
              ·
                refine ⟨27087601301759667230460481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36116801735679556307280641 27087601301759667230460481)
                ·
                  refine ⟨20315700976319750422845361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27087601301759667230460481 20315700976319750422845361)
                  ·
                    refine ⟨15236775732239812817134021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20315700976319750422845361 15236775732239812817134021)
                    ·
                      refine ⟨2856895449794964903212629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15236775732239812817134021 2856895449794964903212629)
                      ·
                        rfl

theorem cell23_5563784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5563784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563784 prefixEnd_5563784 := by exact prefixLift 5563784
  have htrace : WordTrace (prefixWord ++ tailWord_5563784) baseStart_5563784 baseEnd_5563784 := by
    simpa [prefixWord, tailWord_5563784, baseEnd_5563784] using wordTrace_append hprefix tailTrace_5563784
  have hstable : (prefixWord ++ tailWord_5563784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563784).length < 2 ^ (prefixWord ++ tailWord_5563784).sum := by decide
  have hdescent : baseEnd_5563784 < baseStart_5563784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563817 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_5563817 : Nat := 118140960795 + 5563817 * 2 ^ 59
def prefixEnd_5563817 : Nat := 4983230072969 + 3 ^ 40 * 5563817 * 2
def baseEnd_5563817 : Nat := 2856912394656563274099977

theorem tailTrace_5563817 : CollatzResearch.WordTrace tailWord_5563817 prefixEnd_5563817 2856912394656563274099977 := by
  unfold tailWord_5563817
  simp only [CollatzResearch.WordTrace]
  refine ⟨202929077284248708137489705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135286051522832472091659803 202929077284248708137489705)
  ·
    refine ⟨152196807963186531103117279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202929077284248708137489705 152196807963186531103117279)
    ·
      refine ⟨228295211944779796654675919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152196807963186531103117279 228295211944779796654675919)
      ·
        refine ⟨342442817917169694982013879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228295211944779796654675919 342442817917169694982013879)
        ·
          refine ⟨513664226875754542473020819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342442817917169694982013879 513664226875754542473020819)
          ·
            refine ⟨770496340313631813709531229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513664226875754542473020819 770496340313631813709531229)
            ·
              refine ⟨288936127617611930141074211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770496340313631813709531229 288936127617611930141074211)
              ·
                refine ⟨433404191426417895211611317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288936127617611930141074211 433404191426417895211611317)
                ·
                  refine ⟨40631642946226677676088561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433404191426417895211611317 40631642946226677676088561)
                  ·
                    refine ⟨30473732209670008257066421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40631642946226677676088561 30473732209670008257066421)
                    ·
                      refine ⟨2856912394656563274099977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30473732209670008257066421 2856912394656563274099977)
                      ·
                        rfl

theorem cell23_5563817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_5563817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563817 prefixEnd_5563817 := by exact prefixLift 5563817
  have htrace : WordTrace (prefixWord ++ tailWord_5563817) baseStart_5563817 baseEnd_5563817 := by
    simpa [prefixWord, tailWord_5563817, baseEnd_5563817] using wordTrace_append hprefix tailTrace_5563817
  have hstable : (prefixWord ++ tailWord_5563817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563817).length < 2 ^ (prefixWord ++ tailWord_5563817).sum := by decide
  have hdescent : baseEnd_5563817 < baseStart_5563817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
