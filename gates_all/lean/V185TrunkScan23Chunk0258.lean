import V185TrunkScan23Chunk0257

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1526298 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1526298 : Nat := 118140960795 + 1526298 * 2 ^ 59
def prefixEnd_1526298 : Nat := 4983230072969 + 3 ^ 40 * 1526298 * 2
def baseEnd_1526298 : Nat := 783724495996174585755689

theorem tailTrace_1526298 : CollatzResearch.WordTrace tailWord_1526298 prefixEnd_1526298 783724495996174585755689 := by
  unfold tailWord_1526298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917165356122622947608887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37112440949660327860290365 13917165356122622947608887)
  ·
    refine ⟨20875748034183934421413331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917165356122622947608887 20875748034183934421413331)
    ·
      refine ⟨31313622051275901632119997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20875748034183934421413331 31313622051275901632119997)
      ·
        refine ⟨11742608269228463112044999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31313622051275901632119997 11742608269228463112044999)
        ·
          refine ⟨17613912403842694668067499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742608269228463112044999 17613912403842694668067499)
          ·
            refine ⟨26420868605764042002101249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613912403842694668067499 26420868605764042002101249)
            ·
              refine ⟨19815651454323031501575937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26420868605764042002101249 19815651454323031501575937)
              ·
                refine ⟨14861738590742273626181953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19815651454323031501575937 14861738590742273626181953)
                ·
                  refine ⟨11146303943056705219636465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14861738590742273626181953 11146303943056705219636465)
                  ·
                    refine ⟨8359727957292528914727349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11146303943056705219636465 8359727957292528914727349)
                    ·
                      refine ⟨783724495996174585755689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8359727957292528914727349 783724495996174585755689)
                      ·
                        rfl

theorem cell23_1526298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1526298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526298 prefixEnd_1526298 := by exact prefixLift 1526298
  have htrace : WordTrace (prefixWord ++ tailWord_1526298) baseStart_1526298 baseEnd_1526298 := by
    simpa [prefixWord, tailWord_1526298, baseEnd_1526298] using wordTrace_append hprefix tailTrace_1526298
  have hstable : (prefixWord ++ tailWord_1526298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526298).length < 2 ^ (prefixWord ++ tailWord_1526298).sum := by decide
  have hdescent : baseEnd_1526298 < baseStart_1526298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526340 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1526340 : Nat := 118140960795 + 1526340 * 2 ^ 59
def prefixEnd_1526340 : Nat := 4983230072969 + 3 ^ 40 * 1526340 * 2
def baseEnd_1526340 : Nat := 783746062183663421430497

theorem tailTrace_1526340 : CollatzResearch.WordTrace tailWord_1526340 prefixEnd_1526340 783746062183663421430497 := by
  unfold tailWord_1526340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835096645169166481732237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37113462193558888642309649 27835096645169166481732237)
  ·
    refine ⟨10438161241938437430649589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27835096645169166481732237 10438161241938437430649589)
    ·
      refine ⟨978577616431728509123399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10438161241938437430649589 978577616431728509123399)
      ·
        refine ⟨1467866424647592763685099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978577616431728509123399 1467866424647592763685099)
        ·
          refine ⟨2201799636971389145527649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467866424647592763685099 2201799636971389145527649)
          ·
            refine ⟨1651349727728541859145737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201799636971389145527649 1651349727728541859145737)
            ·
              refine ⟨1238512295796406394359303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651349727728541859145737 1238512295796406394359303)
              ·
                refine ⟨1857768443694609591538955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238512295796406394359303 1857768443694609591538955)
                ·
                  refine ⟨2786652665541914387308433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857768443694609591538955 2786652665541914387308433)
                  ·
                    refine ⟨2089989499156435790481325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2786652665541914387308433 2089989499156435790481325)
                    ·
                      refine ⟨783746062183663421430497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2089989499156435790481325 783746062183663421430497)
                      ·
                        rfl

theorem cell23_1526340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1526340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526340 prefixEnd_1526340 := by exact prefixLift 1526340
  have htrace : WordTrace (prefixWord ++ tailWord_1526340) baseStart_1526340 baseEnd_1526340 := by
    simpa [prefixWord, tailWord_1526340, baseEnd_1526340] using wordTrace_append hprefix tailTrace_1526340
  have hstable : (prefixWord ++ tailWord_1526340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526340).length < 2 ^ (prefixWord ++ tailWord_1526340).sum := by decide
  have hdescent : baseEnd_1526340 < baseStart_1526340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526346 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_1526346 : Nat := 118140960795 + 1526346 * 2 ^ 59
def prefixEnd_1526346 : Nat := 4983230072969 + 3 ^ 40 * 1526346 * 2
def baseEnd_1526346 : Nat := 783749143067590397955469

theorem tailTrace_1526346 : CollatzResearch.WordTrace tailWord_1526346 prefixEnd_1526346 783749143067590397955469 := by
  unfold tailWord_1526346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917603032079148997045723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37113608085544397325455261 13917603032079148997045723)
  ·
    refine ⟨20876404548118723495568585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917603032079148997045723 20876404548118723495568585)
    ·
      refine ⟨15657303411089042621676439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20876404548118723495568585 15657303411089042621676439)
      ·
        refine ⟨23485955116633563932514659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15657303411089042621676439 23485955116633563932514659)
        ·
          refine ⟨35228932674950345898771989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23485955116633563932514659 35228932674950345898771989)
          ·
            refine ⟨1651356219138297464004937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35228932674950345898771989 1651356219138297464004937)
            ·
              refine ⟨1238517164353723098003703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651356219138297464004937 1238517164353723098003703)
              ·
                refine ⟨1857775746530584647005555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238517164353723098003703 1857775746530584647005555)
                ·
                  refine ⟨2786663619795876970508333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857775746530584647005555 2786663619795876970508333)
                  ·
                    refine ⟨1044998857423453863940625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2786663619795876970508333 1044998857423453863940625)
                    ·
                      refine ⟨783749143067590397955469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1044998857423453863940625 783749143067590397955469)
                      ·
                        rfl

theorem cell23_1526346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_1526346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526346 prefixEnd_1526346 := by exact prefixLift 1526346
  have htrace : WordTrace (prefixWord ++ tailWord_1526346) baseStart_1526346 baseEnd_1526346 := by
    simpa [prefixWord, tailWord_1526346, baseEnd_1526346] using wordTrace_append hprefix tailTrace_1526346
  have hstable : (prefixWord ++ tailWord_1526346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526346).length < 2 ^ (prefixWord ++ tailWord_1526346).sum := by decide
  have hdescent : baseEnd_1526346 < baseStart_1526346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526348 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 9]
def baseStart_1526348 : Nat := 118140960795 + 1526348 * 2 ^ 59
def prefixEnd_1526348 : Nat := 4983230072969 + 3 ^ 40 * 1526348 * 2
def baseEnd_1526348 : Nat := 87083352225433265570051

theorem tailTrace_1526348 : CollatzResearch.WordTrace tailWord_1526348 prefixEnd_1526348 87083352225433265570051 := by
  unfold tailWord_1526348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835242537154675164877849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37113656716206233553170465 27835242537154675164877849)
  ·
    refine ⟨20876431902866006373658387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27835242537154675164877849 20876431902866006373658387)
    ·
      refine ⟨31314647854299009560487581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20876431902866006373658387 31314647854299009560487581)
      ·
        refine ⟨11742992945362128585182843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31314647854299009560487581 11742992945362128585182843)
        ·
          refine ⟨17614489418043192877774265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742992945362128585182843 17614489418043192877774265)
          ·
            refine ⟨13210867063532394658330699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17614489418043192877774265 13210867063532394658330699)
            ·
              refine ⟨19816300595298591987496049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210867063532394658330699 19816300595298591987496049)
              ·
                refine ⟨14862225446473943990622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19816300595298591987496049 14862225446473943990622037)
                ·
                  refine ⟨87083352225433265570051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14862225446473943990622037 87083352225433265570051)
                  ·
                    rfl

theorem cell23_1526348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_1526348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526348 prefixEnd_1526348 := by exact prefixLift 1526348
  have htrace : WordTrace (prefixWord ++ tailWord_1526348) baseStart_1526348 baseEnd_1526348 := by
    simpa [prefixWord, tailWord_1526348, baseEnd_1526348] using wordTrace_append hprefix tailTrace_1526348
  have hstable : (prefixWord ++ tailWord_1526348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526348).length < 2 ^ (prefixWord ++ tailWord_1526348).sum := by decide
  have hdescent : baseEnd_1526348 < baseStart_1526348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526376 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1526376 : Nat := 118140960795 + 1526376 * 2 ^ 59
def prefixEnd_1526376 : Nat := 4983230072969 + 3 ^ 40 * 1526376 * 2
def baseEnd_1526376 : Nat := 783764547487225280580331

theorem tailTrace_1526376 : CollatzResearch.WordTrace tailWord_1526376 prefixEnd_1526376 783764547487225280580331 := by
  unfold tailWord_1526376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835753159103955555887491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37114337545471940741183321 27835753159103955555887491)
  ·
    refine ⟨41753629738655933333831237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27835753159103955555887491 41753629738655933333831237)
    ·
      refine ⟨7828805575997987500093357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41753629738655933333831237 7828805575997987500093357)
      ·
        refine ⟨2935802090999245312535009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7828805575997987500093357 2935802090999245312535009)
        ·
          refine ⟨2201851568249433984401257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2935802090999245312535009 2201851568249433984401257)
          ·
            refine ⟨1651388676187075488300943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201851568249433984401257 1651388676187075488300943)
            ·
              refine ⟨2477083014280613232451415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651388676187075488300943 2477083014280613232451415)
              ·
                refine ⟨3715624521420919848677123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477083014280613232451415 3715624521420919848677123)
                ·
                  refine ⟨5573436782131379773015685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715624521420919848677123 5573436782131379773015685)
                  ·
                    refine ⟨1045019396649633707440441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573436782131379773015685 1045019396649633707440441)
                    ·
                      refine ⟨783764547487225280580331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045019396649633707440441 783764547487225280580331)
                      ·
                        rfl

theorem cell23_1526376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1526376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526376 prefixEnd_1526376 := by exact prefixLift 1526376
  have htrace : WordTrace (prefixWord ++ tailWord_1526376) baseStart_1526376 baseEnd_1526376 := by
    simpa [prefixWord, tailWord_1526376, baseEnd_1526376] using wordTrace_append hprefix tailTrace_1526376
  have hstable : (prefixWord ++ tailWord_1526376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526376).length < 2 ^ (prefixWord ++ tailWord_1526376).sum := by decide
  have hdescent : baseEnd_1526376 < baseStart_1526376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526415 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_1526415 : Nat := 118140960795 + 1526415 * 2 ^ 59
def prefixEnd_1526415 : Nat := 4983230072969 + 3 ^ 40 * 1526415 * 2
def baseEnd_1526415 : Nat := 783784573232750627992651

theorem tailTrace_1526415 : CollatzResearch.WordTrace tailWord_1526415 prefixEnd_1526415 783784573232750627992651 := by
  unfold tailWord_1526415
  simp only [CollatzResearch.WordTrace]
  refine ⟨55672928765066620772444699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37115285843377747181629799 55672928765066620772444699)
  ·
    refine ⟨83509393147599931158667049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55672928765066620772444699 83509393147599931158667049)
    ·
      refine ⟨62632044860699948369000287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83509393147599931158667049 62632044860699948369000287)
      ·
        refine ⟨93948067291049922553500431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62632044860699948369000287 93948067291049922553500431)
        ·
          refine ⟨140922100936574883830250647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93948067291049922553500431 140922100936574883830250647)
          ·
            refine ⟨211383151404862325745375971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140922100936574883830250647 211383151404862325745375971)
            ·
              refine ⟨317074727107293488618063957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211383151404862325745375971 317074727107293488618063957)
              ·
                refine ⟨3715719458288595569742937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 317074727107293488618063957 3715719458288595569742937)
                ·
                  refine ⟨2786789593716446677307203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715719458288595569742937 2786789593716446677307203)
                  ·
                    refine ⟨4180184390574670015960805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786789593716446677307203 4180184390574670015960805)
                    ·
                      refine ⟨783784573232750627992651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4180184390574670015960805 783784573232750627992651)
                      ·
                        rfl

theorem cell23_1526415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_1526415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526415 prefixEnd_1526415 := by exact prefixLift 1526415
  have htrace : WordTrace (prefixWord ++ tailWord_1526415) baseStart_1526415 baseEnd_1526415 := by
    simpa [prefixWord, tailWord_1526415, baseEnd_1526415] using wordTrace_append hprefix tailTrace_1526415
  have hstable : (prefixWord ++ tailWord_1526415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526415).length < 2 ^ (prefixWord ++ tailWord_1526415).sum := by decide
  have hdescent : baseEnd_1526415 < baseStart_1526415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526435 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1526435 : Nat := 118140960795 + 1526435 * 2 ^ 59
def prefixEnd_1526435 : Nat := 4983230072969 + 3 ^ 40 * 1526435 * 2
def baseEnd_1526435 : Nat := 783794842845840549742559

theorem tailTrace_1526435 : CollatzResearch.WordTrace tailWord_1526435 prefixEnd_1526435 783794842845840549742559 := by
  unfold tailWord_1526435
  simp only [CollatzResearch.WordTrace]
  refine ⟨55673658224994164188172759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37115772149996109458781839 55673658224994164188172759)
  ·
    refine ⟨83510487337491246282259139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55673658224994164188172759 83510487337491246282259139)
    ·
      refine ⟨125265731006236869423388709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83510487337491246282259139 125265731006236869423388709)
      ·
        refine ⟨23487324563669413016885383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125265731006236869423388709 23487324563669413016885383)
        ·
          refine ⟨35230986845504119525328075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23487324563669413016885383 35230986845504119525328075)
          ·
            refine ⟨52846480268256179287992113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35230986845504119525328075 52846480268256179287992113)
            ·
              refine ⟨39634860201192134465994085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52846480268256179287992113 39634860201192134465994085)
              ·
                refine ⟨7431536287723525212373891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39634860201192134465994085 7431536287723525212373891)
                ·
                  refine ⟨11147304431585287818560837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431536287723525212373891 11147304431585287818560837)
                  ·
                    refine ⟨2090119580922241465980157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11147304431585287818560837 2090119580922241465980157)
                    ·
                      refine ⟨783794842845840549742559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090119580922241465980157 783794842845840549742559)
                      ·
                        rfl

theorem cell23_1526435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1526435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526435 prefixEnd_1526435 := by exact prefixLift 1526435
  have htrace : WordTrace (prefixWord ++ tailWord_1526435) baseStart_1526435 baseEnd_1526435 := by
    simpa [prefixWord, tailWord_1526435, baseEnd_1526435] using wordTrace_append hprefix tailTrace_1526435
  have hstable : (prefixWord ++ tailWord_1526435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526435).length < 2 ^ (prefixWord ++ tailWord_1526435).sum := by decide
  have hdescent : baseEnd_1526435 < baseStart_1526435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526472 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 6]
def baseStart_1526472 : Nat := 118140960795 + 1526472 * 2 ^ 59
def prefixEnd_1526472 : Nat := 4983230072969 + 3 ^ 40 * 1526472 * 2
def baseEnd_1526472 : Nat := 87090426847784100553321

theorem tailTrace_1526472 : CollatzResearch.WordTrace tailWord_1526472 prefixEnd_1526472 87090426847784100553321 := by
  unfold tailWord_1526472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27837503862930059753634835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37116671817240079671513113 27837503862930059753634835)
  ·
    refine ⟨41756255794395089630452253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27837503862930059753634835 41756255794395089630452253)
    ·
      refine ⟨15658595922898158611419595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41756255794395089630452253 15658595922898158611419595)
      ·
        refine ⟨23487893884347237917129393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15658595922898158611419595 23487893884347237917129393)
        ·
          refine ⟨17615920413260428437847045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23487893884347237917129393 17615920413260428437847045)
          ·
            refine ⟨3302985077486330332096321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17615920413260428437847045 3302985077486330332096321)
            ·
              refine ⟨2477238808114747749072241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302985077486330332096321 2477238808114747749072241)
              ·
                refine ⟨1857929106086060811804181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477238808114747749072241 1857929106086060811804181)
                ·
                  refine ⟨87090426847784100553321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1857929106086060811804181 87090426847784100553321)
                  ·
                    rfl

theorem cell23_1526472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_1526472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526472 prefixEnd_1526472 := by exact prefixLift 1526472
  have htrace : WordTrace (prefixWord ++ tailWord_1526472) baseStart_1526472 baseEnd_1526472 := by
    simpa [prefixWord, tailWord_1526472, baseEnd_1526472] using wordTrace_append hprefix tailTrace_1526472
  have hstable : (prefixWord ++ tailWord_1526472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526472).length < 2 ^ (prefixWord ++ tailWord_1526472).sum := by decide
  have hdescent : baseEnd_1526472 < baseStart_1526472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526476 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_1526476 : Nat := 118140960795 + 1526476 * 2 ^ 59
def prefixEnd_1526476 : Nat := 4983230072969 + 3 ^ 40 * 1526476 * 2
def baseEnd_1526476 : Nat := 261271965184224963109957

theorem tailTrace_1526476 : CollatzResearch.WordTrace tailWord_1526476 prefixEnd_1526476 261271965184224963109957 := by
  unfold tailWord_1526476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27837576808922814095207641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37116769078563752126943521 27837576808922814095207641)
  ·
    refine ⟨20878182606692110571405731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27837576808922814095207641 20878182606692110571405731)
    ·
      refine ⟨31317273910038165857108597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20878182606692110571405731 31317273910038165857108597)
      ·
        refine ⟨2935994429066078049103931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31317273910038165857108597 2935994429066078049103931)
        ·
          refine ⟨4403991643599117073655897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935994429066078049103931 4403991643599117073655897)
          ·
            refine ⟨3302993732699337805241923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403991643599117073655897 3302993732699337805241923)
            ·
              refine ⟨4954490599049006707862885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302993732699337805241923 4954490599049006707862885)
              ·
                refine ⟨928966987321688757724291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4954490599049006707862885 928966987321688757724291)
                ·
                  refine ⟨1393450480982533136586437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928966987321688757724291 1393450480982533136586437)
                  ·
                    refine ⟨261271965184224963109957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1393450480982533136586437 261271965184224963109957)
                    ·
                      rfl

theorem cell23_1526476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_1526476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526476 prefixEnd_1526476 := by exact prefixLift 1526476
  have htrace : WordTrace (prefixWord ++ tailWord_1526476) baseStart_1526476 baseEnd_1526476 := by
    simpa [prefixWord, tailWord_1526476, baseEnd_1526476] using wordTrace_append hprefix tailTrace_1526476
  have hstable : (prefixWord ++ tailWord_1526476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526476).length < 2 ^ (prefixWord ++ tailWord_1526476).sum := by decide
  have hdescent : baseEnd_1526476 < baseStart_1526476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526499 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1526499 : Nat := 118140960795 + 1526499 * 2 ^ 59
def prefixEnd_1526499 : Nat := 4983230072969 + 3 ^ 40 * 1526499 * 2
def baseEnd_1526499 : Nat := 783827705607728299342265

theorem tailTrace_1526499 : CollatzResearch.WordTrace tailWord_1526499 prefixEnd_1526499 783827705607728299342265 := by
  unfold tailWord_1526499
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675992496762303118502551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37117328331174868745668367 55675992496762303118502551)
  ·
    refine ⟨83513988745143454677753827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55675992496762303118502551 83513988745143454677753827)
    ·
      refine ⟨125270983117715182016630741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83513988745143454677753827 125270983117715182016630741)
      ·
        refine ⟨2936038666821449578514783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125270983117715182016630741 2936038666821449578514783)
        ·
          refine ⟨4404058000232174367772175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936038666821449578514783 4404058000232174367772175)
          ·
            refine ⟨6606087000348261551658263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404058000232174367772175 6606087000348261551658263)
            ·
              refine ⟨9909130500522392327487395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606087000348261551658263 9909130500522392327487395)
              ·
                refine ⟨14863695750783588491231093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909130500522392327487395 14863695750783588491231093)
                ·
                  refine ⟨1393471476635961421052915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14863695750783588491231093 1393471476635961421052915)
                  ·
                    refine ⟨2090207214953942131579373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393471476635961421052915 2090207214953942131579373)
                    ·
                      refine ⟨783827705607728299342265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090207214953942131579373 783827705607728299342265)
                      ·
                        rfl

theorem cell23_1526499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1526499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526499 prefixEnd_1526499 := by exact prefixLift 1526499
  have htrace : WordTrace (prefixWord ++ tailWord_1526499) baseStart_1526499 baseEnd_1526499 := by
    simpa [prefixWord, tailWord_1526499, baseEnd_1526499] using wordTrace_append hprefix tailTrace_1526499
  have hstable : (prefixWord ++ tailWord_1526499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526499).length < 2 ^ (prefixWord ++ tailWord_1526499).sum := by decide
  have hdescent : baseEnd_1526499 < baseStart_1526499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526509 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1526509 : Nat := 118140960795 + 1526509 * 2 ^ 59
def prefixEnd_1526509 : Nat := 4983230072969 + 3 ^ 40 * 1526509 * 2
def baseEnd_1526509 : Nat := 783832840414273260217219

theorem tailTrace_1526509 : CollatzResearch.WordTrace tailWord_1526509 prefixEnd_1526509 783832840414273260217219 := by
  unfold tailWord_1526509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55676357226726074826366581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37117571484484049884244387 55676357226726074826366581)
  ·
    refine ⟨5219658490005569514971867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55676357226726074826366581 5219658490005569514971867)
    ·
      refine ⟨7829487735008354272457801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219658490005569514971867 7829487735008354272457801)
      ·
        refine ⟨5872115801256265704343351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829487735008354272457801 5872115801256265704343351)
        ·
          refine ⟨8808173701884398556515027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872115801256265704343351 8808173701884398556515027)
          ·
            refine ⟨13212260552826597834772541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8808173701884398556515027 13212260552826597834772541)
            ·
              refine ⟨4954597707309974188039703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13212260552826597834772541 4954597707309974188039703)
              ·
                refine ⟨7431896560964961282059555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954597707309974188039703 7431896560964961282059555)
                ·
                  refine ⟨11147844841447441923089333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431896560964961282059555 11147844841447441923089333)
                  ·
                    refine ⟨1045110453885697680289625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11147844841447441923089333 1045110453885697680289625)
                    ·
                      refine ⟨783832840414273260217219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045110453885697680289625 783832840414273260217219)
                      ·
                        rfl

theorem cell23_1526509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1526509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526509 prefixEnd_1526509 := by exact prefixLift 1526509
  have htrace : WordTrace (prefixWord ++ tailWord_1526509) baseStart_1526509 baseEnd_1526509 := by
    simpa [prefixWord, tailWord_1526509, baseEnd_1526509] using wordTrace_append hprefix tailTrace_1526509
  have hstable : (prefixWord ++ tailWord_1526509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526509).length < 2 ^ (prefixWord ++ tailWord_1526509).sum := by decide
  have hdescent : baseEnd_1526509 < baseStart_1526509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526556 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1526556 : Nat := 118140960795 + 1526556 * 2 ^ 59
def prefixEnd_1526556 : Nat := 4983230072969 + 3 ^ 40 * 1526556 * 2
def baseEnd_1526556 : Nat := 783856974005034576329503

theorem tailTrace_1526556 : CollatzResearch.WordTrace tailWord_1526556 prefixEnd_1526556 783856974005034576329503 := by
  unfold tailWord_1526556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27839035728777900926663761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37118714305037201235551681 27839035728777900926663761)
  ·
    refine ⟨20879276796583425694997821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27839035728777900926663761 20879276796583425694997821)
    ·
      refine ⟨7829728798718784635624183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20879276796583425694997821 7829728798718784635624183)
      ·
        refine ⟨11744593198078176953436275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829728798718784635624183 11744593198078176953436275)
        ·
          refine ⟨17616889797117265430154413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744593198078176953436275 17616889797117265430154413)
          ·
            refine ⟨6606333673918974536307905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17616889797117265430154413 6606333673918974536307905)
            ·
              refine ⟨4954750255439230902230929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606333673918974536307905 4954750255439230902230929)
              ·
                refine ⟨3716062691579423176673197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954750255439230902230929 3716062691579423176673197)
                ·
                  refine ⟨1393523509342283691252449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3716062691579423176673197 1393523509342283691252449)
                  ·
                    refine ⟨1045142632006712768439337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1393523509342283691252449 1045142632006712768439337)
                    ·
                      refine ⟨783856974005034576329503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045142632006712768439337 783856974005034576329503)
                      ·
                        rfl

theorem cell23_1526556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1526556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526556 prefixEnd_1526556 := by exact prefixLift 1526556
  have htrace : WordTrace (prefixWord ++ tailWord_1526556) baseStart_1526556 baseEnd_1526556 := by
    simpa [prefixWord, tailWord_1526556, baseEnd_1526556] using wordTrace_append hprefix tailTrace_1526556
  have hstable : (prefixWord ++ tailWord_1526556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526556).length < 2 ^ (prefixWord ++ tailWord_1526556).sum := by decide
  have hdescent : baseEnd_1526556 < baseStart_1526556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526559 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1526559 : Nat := 118140960795 + 1526559 * 2 ^ 59
def prefixEnd_1526559 : Nat := 4983230072969 + 3 ^ 40 * 1526559 * 2
def baseEnd_1526559 : Nat := 783858514446998064591989

theorem tailTrace_1526559 : CollatzResearch.WordTrace tailWord_1526559 prefixEnd_1526559 783858514446998064591989 := by
  unfold tailWord_1526559
  simp only [CollatzResearch.WordTrace]
  refine ⟨55678180876544933365686731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37118787251029955577124487 55678180876544933365686731)
  ·
    refine ⟨83517271314817400048530097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55678180876544933365686731 83517271314817400048530097)
    ·
      refine ⟨62637953486113050036397573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83517271314817400048530097 62637953486113050036397573)
      ·
        refine ⟨11744616278646196881824545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62637953486113050036397573 11744616278646196881824545)
        ·
          refine ⟨8808462208984647661368409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744616278646196881824545 8808462208984647661368409)
          ·
            refine ⟨6606346656738485746026307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8808462208984647661368409 6606346656738485746026307)
            ·
              refine ⟨9909519985107728619039461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606346656738485746026307 9909519985107728619039461)
              ·
                refine ⟨1858034997207699116069899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9909519985107728619039461 1858034997207699116069899)
                ·
                  refine ⟨2787052495811548674104849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858034997207699116069899 2787052495811548674104849)
                  ·
                    refine ⟨2090289371858661505578637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2787052495811548674104849 2090289371858661505578637)
                    ·
                      refine ⟨783858514446998064591989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090289371858661505578637 783858514446998064591989)
                      ·
                        rfl

theorem cell23_1526559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1526559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526559 prefixEnd_1526559 := by exact prefixLift 1526559
  have htrace : WordTrace (prefixWord ++ tailWord_1526559) baseStart_1526559 baseEnd_1526559 := by
    simpa [prefixWord, tailWord_1526559, baseEnd_1526559] using wordTrace_append hprefix tailTrace_1526559
  have hstable : (prefixWord ++ tailWord_1526559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526559).length < 2 ^ (prefixWord ++ tailWord_1526559).sum := by decide
  have hdescent : baseEnd_1526559 < baseStart_1526559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526562 : List Nat := [3, 3, 1, 1, 2, 3, 1, 9]
def baseStart_1526562 : Nat := 118140960795 + 1526562 * 2 ^ 59
def prefixEnd_1526562 : Nat := 4983230072969 + 3 ^ 40 * 1526562 * 2
def baseEnd_1526562 : Nat := 29031853884776353809425

theorem tailTrace_1526562 : CollatzResearch.WordTrace tailWord_1526562 prefixEnd_1526562 29031853884776353809425 := by
  unfold tailWord_1526562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919572573883516219511485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37118860197022709918697293 13919572573883516219511485)
  ·
    refine ⟨5219839715206318582316807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13919572573883516219511485 5219839715206318582316807)
    ·
      refine ⟨7829759572809477873475211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219839715206318582316807 7829759572809477873475211)
      ·
        refine ⟨11744639359214216810212817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829759572809477873475211 11744639359214216810212817)
        ·
          refine ⟨8808479519410662607659613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744639359214216810212817 8808479519410662607659613)
          ·
            refine ⟨3303179819778998477872355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8808479519410662607659613 3303179819778998477872355)
            ·
              refine ⟨4954769729668497716808533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303179819778998477872355 4954769729668497716808533)
              ·
                refine ⟨29031853884776353809425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4954769729668497716808533 29031853884776353809425)
                ·
                  rfl

theorem cell23_1526562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_1526562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526562 prefixEnd_1526562 := by exact prefixLift 1526562
  have htrace : WordTrace (prefixWord ++ tailWord_1526562) baseStart_1526562 baseEnd_1526562 := by
    simpa [prefixWord, tailWord_1526562, baseEnd_1526562] using wordTrace_append hprefix tailTrace_1526562
  have hstable : (prefixWord ++ tailWord_1526562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526562).length < 2 ^ (prefixWord ++ tailWord_1526562).sum := by decide
  have hdescent : baseEnd_1526562 < baseStart_1526562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526572 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1526572 : Nat := 118140960795 + 1526572 * 2 ^ 59
def prefixEnd_1526572 : Nat := 4983230072969 + 3 ^ 40 * 1526572 * 2
def baseEnd_1526572 : Nat := 783865189695506513729429

theorem tailTrace_1526572 : CollatzResearch.WordTrace tailWord_1526572 prefixEnd_1526572 783865189695506513729429 := by
  unfold tailWord_1526572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27839327512748918292954985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37119103350331891057273313 27839327512748918292954985)
  ·
    refine ⟨20879495634561688719716239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27839327512748918292954985 20879495634561688719716239)
    ·
      refine ⟨31319243451842533079574359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20879495634561688719716239 31319243451842533079574359)
      ·
        refine ⟨46978865177763799619361539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31319243451842533079574359 46978865177763799619361539)
        ·
          refine ⟨70468297766645699429042309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46978865177763799619361539 70468297766645699429042309)
          ·
            refine ⟨13212805831246068642945433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70468297766645699429042309 13212805831246068642945433)
            ·
              refine ⟨9909604373434551482209075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13212805831246068642945433 9909604373434551482209075)
              ·
                refine ⟨14864406560151827223313613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909604373434551482209075 14864406560151827223313613)
                ·
                  refine ⟨5574152460056935208742605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14864406560151827223313613 5574152460056935208742605)
                  ·
                    refine ⟨2090307172521350703278477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5574152460056935208742605 2090307172521350703278477)
                    ·
                      refine ⟨783865189695506513729429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090307172521350703278477 783865189695506513729429)
                      ·
                        rfl

theorem cell23_1526572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1526572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526572 prefixEnd_1526572 := by exact prefixLift 1526572
  have htrace : WordTrace (prefixWord ++ tailWord_1526572) baseStart_1526572 baseEnd_1526572 := by
    simpa [prefixWord, tailWord_1526572, baseEnd_1526572] using wordTrace_append hprefix tailTrace_1526572
  have hstable : (prefixWord ++ tailWord_1526572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526572).length < 2 ^ (prefixWord ++ tailWord_1526572).sum := by decide
  have hdescent : baseEnd_1526572 < baseStart_1526572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526590 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_1526590 : Nat := 118140960795 + 1526590 * 2 ^ 59
def prefixEnd_1526590 : Nat := 4983230072969 + 3 ^ 40 * 1526590 * 2
def baseEnd_1526590 : Nat := 783874432347287443304347

theorem tailTrace_1526590 : CollatzResearch.WordTrace tailWord_1526590 prefixEnd_1526590 783874432347287443304347 := by
  unfold tailWord_1526590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959913942429078207508153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37119541026288417106710149 6959913942429078207508153)
  ·
    refine ⟨5219935456821808655631115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6959913942429078207508153 5219935456821808655631115)
    ·
      refine ⟨7829903185232712983446673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219935456821808655631115 7829903185232712983446673)
      ·
        refine ⟨5872427388924534737585005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829903185232712983446673 5872427388924534737585005)
        ·
          refine ⟨2202160270846700526594377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5872427388924534737585005 2202160270846700526594377)
          ·
            refine ⟨1651620203135025394945783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202160270846700526594377 1651620203135025394945783)
            ·
              refine ⟨2477430304702538092418675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651620203135025394945783 2477430304702538092418675)
              ·
                refine ⟨3716145457053807138628013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477430304702538092418675 3716145457053807138628013)
                ·
                  refine ⟨1393554546395177676985505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3716145457053807138628013 1393554546395177676985505)
                  ·
                    refine ⟨1045165909796383257739129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1393554546395177676985505 1045165909796383257739129)
                    ·
                      refine ⟨783874432347287443304347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045165909796383257739129 783874432347287443304347)
                      ·
                        rfl

theorem cell23_1526590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_1526590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526590 prefixEnd_1526590 := by exact prefixLift 1526590
  have htrace : WordTrace (prefixWord ++ tailWord_1526590) baseStart_1526590 baseEnd_1526590 := by
    simpa [prefixWord, tailWord_1526590, baseEnd_1526590] using wordTrace_append hprefix tailTrace_1526590
  have hstable : (prefixWord ++ tailWord_1526590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526590).length < 2 ^ (prefixWord ++ tailWord_1526590).sum := by decide
  have hdescent : baseEnd_1526590 < baseStart_1526590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526596 : List Nat := [2, 3, 4, 2, 1, 1, 2, 8]
def baseStart_1526596 : Nat := 118140960795 + 1526596 * 2 ^ 59
def prefixEnd_1526596 : Nat := 4983230072969 + 3 ^ 40 * 1526596 * 2
def baseEnd_1526596 : Nat := 29032500490044978512197

theorem tailTrace_1526596 : CollatzResearch.WordTrace tailWord_1526596 prefixEnd_1526596 29032500490044978512197 := by
  unfold tailWord_1526596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27839765188705444342391821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37119686918273925789855761 27839765188705444342391821)
  ·
    refine ⟨10439911945764541628396933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27839765188705444342391821 10439911945764541628396933)
    ·
      refine ⟨1957483489830851555324425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10439911945764541628396933 1957483489830851555324425)
      ·
        refine ⟨1468112617373138666493319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957483489830851555324425 1468112617373138666493319)
        ·
          refine ⟨2202168926059707999739979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468112617373138666493319 2202168926059707999739979)
          ·
            refine ⟨3303253389089561999609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202168926059707999739979 3303253389089561999609969)
            ·
              refine ⟨2477440041817171499707477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303253389089561999609969 2477440041817171499707477)
              ·
                refine ⟨29032500490044978512197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2477440041817171499707477 29032500490044978512197)
                ·
                  rfl

theorem cell23_1526596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 8].length) (baseStart_1526596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526596 prefixEnd_1526596 := by exact prefixLift 1526596
  have htrace : WordTrace (prefixWord ++ tailWord_1526596) baseStart_1526596 baseEnd_1526596 := by
    simpa [prefixWord, tailWord_1526596, baseEnd_1526596] using wordTrace_append hprefix tailTrace_1526596
  have hstable : (prefixWord ++ tailWord_1526596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526596).length < 2 ^ (prefixWord ++ tailWord_1526596).sum := by decide
  have hdescent : baseEnd_1526596 < baseStart_1526596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_1526599 : Nat := 118140960795 + 1526599 * 2 ^ 59
def prefixEnd_1526599 : Nat := 4983230072969 + 3 ^ 40 * 1526599 * 2
def baseEnd_1526599 : Nat := 783879053673177908091805

theorem tailTrace_1526599 : CollatzResearch.WordTrace tailWord_1526599 prefixEnd_1526599 783879053673177908091805 := by
  unfold tailWord_1526599
  simp only [CollatzResearch.WordTrace]
  refine ⟨55679639796400020197142851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37119759864266680131428567 55679639796400020197142851)
  ·
    refine ⟨83519459694600030295714277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55679639796400020197142851 83519459694600030295714277)
    ·
      refine ⟨15659898692737505680446427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83519459694600030295714277 15659898692737505680446427)
      ·
        refine ⟨23489848039106258520669641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15659898692737505680446427 23489848039106258520669641)
        ·
          refine ⟨17617386029329693890502231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23489848039106258520669641 17617386029329693890502231)
          ·
            refine ⟨26426079043994540835753347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17617386029329693890502231 26426079043994540835753347)
            ·
              refine ⟨39639118565991811253630021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26426079043994540835753347 39639118565991811253630021)
              ·
                refine ⟨7432334731123464610055629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39639118565991811253630021 7432334731123464610055629)
                ·
                  refine ⟨2787125524171299228770861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7432334731123464610055629 2787125524171299228770861)
                  ·
                    refine ⟨1045172071564237210789073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787125524171299228770861 1045172071564237210789073)
                    ·
                      refine ⟨783879053673177908091805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045172071564237210789073 783879053673177908091805)
                      ·
                        rfl

theorem cell23_1526599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_1526599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526599 prefixEnd_1526599 := by exact prefixLift 1526599
  have htrace : WordTrace (prefixWord ++ tailWord_1526599) baseStart_1526599 baseEnd_1526599 := by
    simpa [prefixWord, tailWord_1526599, baseEnd_1526599] using wordTrace_append hprefix tailTrace_1526599
  have hstable : (prefixWord ++ tailWord_1526599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526599).length < 2 ^ (prefixWord ++ tailWord_1526599).sum := by decide
  have hdescent : baseEnd_1526599 < baseStart_1526599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526629 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_1526629 : Nat := 118140960795 + 1526629 * 2 ^ 59
def prefixEnd_1526629 : Nat := 4983230072969 + 3 ^ 40 * 1526629 * 2
def baseEnd_1526629 : Nat := 783894458092812790716667

theorem tailTrace_1526629 : CollatzResearch.WordTrace tailWord_1526629 prefixEnd_1526629 783894458092812790716667 := by
  unfold tailWord_1526629
  simp only [CollatzResearch.WordTrace]
  refine ⟨55680733986291335320734941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37120489324194223547156627 55680733986291335320734941)
  ·
    refine ⟨20880275244859250745275603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55680733986291335320734941 20880275244859250745275603)
    ·
      refine ⟨31320412867288876117913405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20880275244859250745275603 31320412867288876117913405)
      ·
        refine ⟨11745154825233328544217527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31320412867288876117913405 11745154825233328544217527)
        ·
          refine ⟨17617732237849992816326291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11745154825233328544217527 17617732237849992816326291)
          ·
            refine ⟨26426598356774989224489437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17617732237849992816326291 26426598356774989224489437)
            ·
              refine ⟨9909974383790620959183539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26426598356774989224489437 9909974383790620959183539)
              ·
                refine ⟨14864961575685931438775309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909974383790620959183539 14864961575685931438775309)
                ·
                  refine ⟨5574360590882224289540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14864961575685931438775309 5574360590882224289540741)
                  ·
                    refine ⟨1045192610790417054288889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574360590882224289540741 1045192610790417054288889)
                    ·
                      refine ⟨783894458092812790716667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045192610790417054288889 783894458092812790716667)
                      ·
                        rfl

theorem cell23_1526629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_1526629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526629 prefixEnd_1526629 := by exact prefixLift 1526629
  have htrace : WordTrace (prefixWord ++ tailWord_1526629) baseStart_1526629 baseEnd_1526629 := by
    simpa [prefixWord, tailWord_1526629, baseEnd_1526629] using wordTrace_append hprefix tailTrace_1526629
  have hstable : (prefixWord ++ tailWord_1526629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526629).length < 2 ^ (prefixWord ++ tailWord_1526629).sum := by decide
  have hdescent : baseEnd_1526629 < baseStart_1526629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526663 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_1526663 : Nat := 118140960795 + 1526663 * 2 ^ 59
def prefixEnd_1526663 : Nat := 4983230072969 + 3 ^ 40 * 1526663 * 2
def baseEnd_1526663 : Nat := 783911916435065657691511

theorem tailTrace_1526663 : CollatzResearch.WordTrace tailWord_1526663 prefixEnd_1526663 783911916435065657691511 := by
  unfold tailWord_1526663
  simp only [CollatzResearch.WordTrace]
  refine ⟨55681974068168159127472643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37121316045445439418315095 55681974068168159127472643)
  ·
    refine ⟨83522961102252238691208965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55681974068168159127472643 83522961102252238691208965)
    ·
      refine ⟨15660555206672294754601681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83522961102252238691208965 15660555206672294754601681)
      ·
        refine ⟨11745416405004221065951261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15660555206672294754601681 11745416405004221065951261)
        ·
          refine ⟨4404531151876582899731723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11745416405004221065951261 4404531151876582899731723)
          ·
            refine ⟨6606796727814874349597585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404531151876582899731723 6606796727814874349597585)
            ·
              refine ⟨4955097545861155762198189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606796727814874349597585 4955097545861155762198189)
              ·
                refine ⟨1858161579697933410824321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4955097545861155762198189 1858161579697933410824321)
                ·
                  refine ⟨1393621184773450058118241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1858161579697933410824321 1393621184773450058118241)
                  ·
                    refine ⟨1045215888580087543588681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1393621184773450058118241 1045215888580087543588681)
                    ·
                      refine ⟨783911916435065657691511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045215888580087543588681 783911916435065657691511)
                      ·
                        rfl

theorem cell23_1526663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_1526663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526663 prefixEnd_1526663 := by exact prefixLift 1526663
  have htrace : WordTrace (prefixWord ++ tailWord_1526663) baseStart_1526663 baseEnd_1526663 := by
    simpa [prefixWord, tailWord_1526663, baseEnd_1526663] using wordTrace_append hprefix tailTrace_1526663
  have hstable : (prefixWord ++ tailWord_1526663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526663).length < 2 ^ (prefixWord ++ tailWord_1526663).sum := by decide
  have hdescent : baseEnd_1526663 < baseStart_1526663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526719 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 6, 2]
def baseStart_1526719 : Nat := 118140960795 + 1526719 * 2 ^ 59
def prefixEnd_1526719 : Nat := 4983230072969 + 3 ^ 40 * 1526719 * 2
def baseEnd_1526719 : Nat := 783940671351717438591253

theorem tailTrace_1526719 : CollatzResearch.WordTrace tailWord_1526719 prefixEnd_1526719 783940671351717438591253 := by
  unfold tailWord_1526719
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684016555965280691511211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37122677703976853794340807 55684016555965280691511211)
  ·
    refine ⟨83526024833947921037266817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55684016555965280691511211 83526024833947921037266817)
    ·
      refine ⟨62644518625460940777950113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83526024833947921037266817 62644518625460940777950113)
      ·
        refine ⟨46983388969095705583462585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62644518625460940777950113 46983388969095705583462585)
        ·
          refine ⟨35237541726821779187596939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46983388969095705583462585 35237541726821779187596939)
          ·
            refine ⟨52856312590232668781395409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35237541726821779187596939 52856312590232668781395409)
            ·
              refine ⟨39642234442674501586046557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52856312590232668781395409 39642234442674501586046557)
              ·
                refine ⟨14865837916002938094767459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39642234442674501586046557 14865837916002938094767459)
                ·
                  refine ⟨22298756874004407142151189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14865837916002938094767459 22298756874004407142151189)
                  ·
                    refine ⟨1045254228468956584788337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22298756874004407142151189 1045254228468956584788337)
                    ·
                      refine ⟨783940671351717438591253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045254228468956584788337 783940671351717438591253)
                      ·
                        rfl

theorem cell23_1526719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_1526719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526719 prefixEnd_1526719 := by exact prefixLift 1526719
  have htrace : WordTrace (prefixWord ++ tailWord_1526719) baseStart_1526719 baseEnd_1526719 := by
    simpa [prefixWord, tailWord_1526719, baseEnd_1526719] using wordTrace_append hprefix tailTrace_1526719
  have hstable : (prefixWord ++ tailWord_1526719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526719).length < 2 ^ (prefixWord ++ tailWord_1526719).sum := by decide
  have hdescent : baseEnd_1526719 < baseStart_1526719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526759 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 8]
def baseStart_1526759 : Nat := 118140960795 + 1526759 * 2 ^ 59
def prefixEnd_1526759 : Nat := 4983230072969 + 3 ^ 40 * 1526759 * 2
def baseEnd_1526759 : Nat := 87106801175321920232341

theorem tailTrace_1526759 : CollatzResearch.WordTrace tailWord_1526759 prefixEnd_1526759 87106801175321920232341 := by
  unfold tailWord_1526759
  simp only [CollatzResearch.WordTrace]
  refine ⟨55685475475820367522967331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37123650317213578348644887 55685475475820367522967331)
  ·
    refine ⟨83528213213730551284450997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55685475475820367522967331 83528213213730551284450997)
    ·
      refine ⟨7830769988787239182917281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83528213213730551284450997 7830769988787239182917281)
      ·
        refine ⟨5873077491590429387187961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7830769988787239182917281 5873077491590429387187961)
        ·
          refine ⟨4404808118692822040390971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5873077491590429387187961 4404808118692822040390971)
          ·
            refine ⟨6607212178039233060586457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404808118692822040390971 6607212178039233060586457)
            ·
              refine ⟨4955409133529424795439843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6607212178039233060586457 4955409133529424795439843)
              ·
                refine ⟨7433113700294137193159765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955409133529424795439843 7433113700294137193159765)
                ·
                  refine ⟨87106801175321920232341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7433113700294137193159765 87106801175321920232341)
                  ·
                    rfl

theorem cell23_1526759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 8].length) (baseStart_1526759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526759 prefixEnd_1526759 := by exact prefixLift 1526759
  have htrace : WordTrace (prefixWord ++ tailWord_1526759) baseStart_1526759 baseEnd_1526759 := by
    simpa [prefixWord, tailWord_1526759, baseEnd_1526759] using wordTrace_append hprefix tailTrace_1526759
  have hstable : (prefixWord ++ tailWord_1526759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526759).length < 2 ^ (prefixWord ++ tailWord_1526759).sum := by decide
  have hdescent : baseEnd_1526759 < baseStart_1526759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526789 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1526789 : Nat := 118140960795 + 1526789 * 2 ^ 59
def prefixEnd_1526789 : Nat := 4983230072969 + 3 ^ 40 * 1526789 * 2
def baseEnd_1526789 : Nat := 261325538332510721571977

theorem tailTrace_1526789 : CollatzResearch.WordTrace tailWord_1526789 prefixEnd_1526789 261325538332510721571977 := by
  unfold tailWord_1526789
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686569665711682646559421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37124379777141121764372947 55686569665711682646559421)
  ·
    refine ⟨20882463624641880992459783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55686569665711682646559421 20882463624641880992459783)
    ·
      refine ⟨31323695436962821488689675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20882463624641880992459783 31323695436962821488689675)
      ·
        refine ⟨46985543155444232233034513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31323695436962821488689675 46985543155444232233034513)
        ·
          refine ⟨35239157366583174174775885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46985543155444232233034513 35239157366583174174775885)
          ·
            refine ⟨13214684012468690315540957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35239157366583174174775885 13214684012468690315540957)
            ·
              refine ⟨4955506504675758868327859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13214684012468690315540957 4955506504675758868327859)
              ·
                refine ⟨7433259757013638302491789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955506504675758868327859 7433259757013638302491789)
                ·
                  refine ⟨2787472408880114363434421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7433259757013638302491789 2787472408880114363434421)
                  ·
                    refine ⟨261325538332510721571977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2787472408880114363434421 261325538332510721571977)
                    ·
                      rfl

theorem cell23_1526789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1526789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526789 prefixEnd_1526789 := by exact prefixLift 1526789
  have htrace : WordTrace (prefixWord ++ tailWord_1526789) baseStart_1526789 baseEnd_1526789 := by
    simpa [prefixWord, tailWord_1526789, baseEnd_1526789] using wordTrace_append hprefix tailTrace_1526789
  have hstable : (prefixWord ++ tailWord_1526789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526789).length < 2 ^ (prefixWord ++ tailWord_1526789).sum := by decide
  have hdescent : baseEnd_1526789 < baseStart_1526789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526803 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 1, 1, 3]
def baseStart_1526803 : Nat := 118140960795 + 1526803 * 2 ^ 59
def prefixEnd_1526803 : Nat := 4983230072969 + 3 ^ 40 * 1526803 * 2
def baseEnd_1526803 : Nat := 783983803726695109940867

theorem tailTrace_1526803 : CollatzResearch.WordTrace tailWord_1526803 prefixEnd_1526803 783983803726695109940867 := by
  unfold tailWord_1526803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55687080287660963037569063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37124720191773975358379375 55687080287660963037569063)
  ·
    refine ⟨83530620431491444556353595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55687080287660963037569063 83530620431491444556353595)
    ·
      refine ⟨125295930647237166834530393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83530620431491444556353595 125295930647237166834530393)
      ·
        refine ⟨93971947985427875125897795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125295930647237166834530393 93971947985427875125897795)
        ·
          refine ⟨140957921978141812688846693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93971947985427875125897795 140957921978141812688846693)
          ·
            refine ⟨26429610370901589879158755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140957921978141812688846693 26429610370901589879158755)
            ·
              refine ⟨39644415556352384818738133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26429610370901589879158755 39644415556352384818738133)
              ·
                refine ⟨929165989602009019189175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39644415556352384818738133 929165989602009019189175)
                ·
                  refine ⟨1393748984403013528783763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929165989602009019189175 1393748984403013528783763)
                  ·
                    refine ⟨2090623476604520293175645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393748984403013528783763 2090623476604520293175645)
                    ·
                      refine ⟨783983803726695109940867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090623476604520293175645 783983803726695109940867)
                      ·
                        rfl

theorem cell23_1526803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 1, 3].length) (baseStart_1526803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526803 prefixEnd_1526803 := by exact prefixLift 1526803
  have htrace : WordTrace (prefixWord ++ tailWord_1526803) baseStart_1526803 baseEnd_1526803 := by
    simpa [prefixWord, tailWord_1526803, baseEnd_1526803] using wordTrace_append hprefix tailTrace_1526803
  have hstable : (prefixWord ++ tailWord_1526803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526803).length < 2 ^ (prefixWord ++ tailWord_1526803).sum := by decide
  have hdescent : baseEnd_1526803 < baseStart_1526803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526854 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1526854 : Nat := 118140960795 + 1526854 * 2 ^ 59
def prefixEnd_1526854 : Nat := 4983230072969 + 3 ^ 40 * 1526854 * 2
def baseEnd_1526854 : Nat := 784009991240074410403133

theorem tailTrace_1526854 : CollatzResearch.WordTrace tailWord_1526854 prefixEnd_1526854 784009991240074410403133 := by
  unfold tailWord_1526854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740279387827381210864863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37125960273650799165117077 1740279387827381210864863)
  ·
    refine ⟨2610419081741071816297295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740279387827381210864863 2610419081741071816297295)
    ·
      refine ⟨3915628622611607724445943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610419081741071816297295 3915628622611607724445943)
      ·
        refine ⟨5873442933917411586668915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915628622611607724445943 5873442933917411586668915)
        ·
          refine ⟨8810164400876117380003373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873442933917411586668915 8810164400876117380003373)
          ·
            refine ⟨3303811650328544017501265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8810164400876117380003373 3303811650328544017501265)
            ·
              refine ⟨2477858737746408013125949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303811650328544017501265 2477858737746408013125949)
              ·
                refine ⟨929197026654903004922231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2477858737746408013125949 929197026654903004922231)
                ·
                  refine ⟨1393795539982354507383347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929197026654903004922231 1393795539982354507383347)
                  ·
                    refine ⟨2090693309973531761075021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1393795539982354507383347 2090693309973531761075021)
                    ·
                      refine ⟨784009991240074410403133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090693309973531761075021 784009991240074410403133)
                      ·
                        rfl

theorem cell23_1526854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1526854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526854 prefixEnd_1526854 := by exact prefixLift 1526854
  have htrace : WordTrace (prefixWord ++ tailWord_1526854) baseStart_1526854 baseEnd_1526854 := by
    simpa [prefixWord, tailWord_1526854, baseEnd_1526854] using wordTrace_append hprefix tailTrace_1526854
  have hstable : (prefixWord ++ tailWord_1526854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526854).length < 2 ^ (prefixWord ++ tailWord_1526854).sum := by decide
  have hdescent : baseEnd_1526854 < baseStart_1526854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526893 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1526893 : Nat := 118140960795 + 1526893 * 2 ^ 59
def prefixEnd_1526893 : Nat := 4983230072969 + 3 ^ 40 * 1526893 * 2
def baseEnd_1526893 : Nat := 784030016985599757815453

theorem tailTrace_1526893 : CollatzResearch.WordTrace tailWord_1526893 prefixEnd_1526893 784030016985599757815453 := by
  unfold tailWord_1526893
  simp only [CollatzResearch.WordTrace]
  refine ⟨55690362857334908408345333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37126908571556605605563555 55690362857334908408345333)
  ·
    refine ⟨5220971517875147663282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55690362857334908408345333 5220971517875147663282375)
    ·
      refine ⟨7831457276812721494923563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220971517875147663282375 7831457276812721494923563)
      ·
        refine ⟨11747185915219082242385345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831457276812721494923563 11747185915219082242385345)
        ·
          refine ⟨8810389436414311681789009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747185915219082242385345 8810389436414311681789009)
          ·
            refine ⟨6607792077310733761341757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810389436414311681789009 6607792077310733761341757)
            ·
              refine ⟨2477922028991525160503159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6607792077310733761341757 2477922028991525160503159)
              ·
                refine ⟨3716883043487287740754739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477922028991525160503159 3716883043487287740754739)
                ·
                  refine ⟨5575324565230931611132109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716883043487287740754739 5575324565230931611132109)
                  ·
                    refine ⟨2090746711961599354174541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5575324565230931611132109 2090746711961599354174541)
                    ·
                      refine ⟨784030016985599757815453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2090746711961599354174541 784030016985599757815453)
                      ·
                        rfl

theorem cell23_1526893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1526893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526893 prefixEnd_1526893 := by exact prefixLift 1526893
  have htrace : WordTrace (prefixWord ++ tailWord_1526893) baseStart_1526893 baseEnd_1526893 := by
    simpa [prefixWord, tailWord_1526893, baseEnd_1526893] using wordTrace_append hprefix tailTrace_1526893
  have hstable : (prefixWord ++ tailWord_1526893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526893).length < 2 ^ (prefixWord ++ tailWord_1526893).sum := by decide
  have hdescent : baseEnd_1526893 < baseStart_1526893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526954 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1526954 : Nat := 118140960795 + 1526954 * 2 ^ 59
def prefixEnd_1526954 : Nat := 4983230072969 + 3 ^ 40 * 1526954 * 2
def baseEnd_1526954 : Nat := 784061339305524019152673

theorem tailTrace_1526954 : CollatzResearch.WordTrace tailWord_1526954 prefixEnd_1526954 784061339305524019152673 := by
  unfold tailWord_1526954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923146927528478956578979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37128391806742610550877277 13923146927528478956578979)
  ·
    refine ⟨20884720391292718434868469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13923146927528478956578979 20884720391292718434868469)
    ·
      refine ⟨1957942536683692353268919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20884720391292718434868469 1957942536683692353268919)
      ·
        refine ⟨2936913805025538529903379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957942536683692353268919 2936913805025538529903379)
        ·
          refine ⟨4405370707538307794855069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936913805025538529903379 4405370707538307794855069)
          ·
            refine ⟨1652014015326865423070651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4405370707538307794855069 1652014015326865423070651)
            ·
              refine ⟨2478021022990298134605977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652014015326865423070651 2478021022990298134605977)
              ·
                refine ⟨1858515767242723600954483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478021022990298134605977 1858515767242723600954483)
                ·
                  refine ⟨2787773650864085401431725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858515767242723600954483 2787773650864085401431725)
                  ·
                    refine ⟨1045415119074032025536897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2787773650864085401431725 1045415119074032025536897)
                    ·
                      refine ⟨784061339305524019152673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045415119074032025536897 784061339305524019152673)
                      ·
                        rfl

theorem cell23_1526954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1526954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526954 prefixEnd_1526954 := by exact prefixLift 1526954
  have htrace : WordTrace (prefixWord ++ tailWord_1526954) baseStart_1526954 baseEnd_1526954 := by
    simpa [prefixWord, tailWord_1526954, baseEnd_1526954] using wordTrace_append hprefix tailTrace_1526954
  have hstable : (prefixWord ++ tailWord_1526954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526954).length < 2 ^ (prefixWord ++ tailWord_1526954).sum := by decide
  have hdescent : baseEnd_1526954 < baseStart_1526954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526990 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_1526990 : Nat := 118140960795 + 1526990 * 2 ^ 59
def prefixEnd_1526990 : Nat := 4983230072969 + 3 ^ 40 * 1526990 * 2
def baseEnd_1526990 : Nat := 87119980512120653144723

theorem tailTrace_1526990 : CollatzResearch.WordTrace tailWord_1526990 prefixEnd_1526990 87119980512120653144723 := by
  unfold tailWord_1526990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961737592247936746828303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37129267158655662649750949 6961737592247936746828303)
  ·
    refine ⟨10442606388371905120242455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6961737592247936746828303 10442606388371905120242455)
    ·
      refine ⟨15663909582557857680363683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10442606388371905120242455 15663909582557857680363683)
      ·
        refine ⟨23495864373836786520545525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15663909582557857680363683 23495864373836786520545525)
        ·
          refine ⟨2202737285047198736301143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23495864373836786520545525 2202737285047198736301143)
          ·
            refine ⟨3304105927570798104451715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202737285047198736301143 3304105927570798104451715)
            ·
              refine ⟨4956158891356197156677573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304105927570798104451715 4956158891356197156677573)
              ·
                refine ⟨929279792129286966877045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4956158891356197156677573 929279792129286966877045)
                ·
                  refine ⟨87119980512120653144723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929279792129286966877045 87119980512120653144723)
                  ·
                    rfl

theorem cell23_1526990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_1526990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1526990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1526990 prefixEnd_1526990 := by exact prefixLift 1526990
  have htrace : WordTrace (prefixWord ++ tailWord_1526990) baseStart_1526990 baseEnd_1526990 := by
    simpa [prefixWord, tailWord_1526990, baseEnd_1526990] using wordTrace_append hprefix tailTrace_1526990
  have hstable : (prefixWord ++ tailWord_1526990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526990).length < 2 ^ (prefixWord ++ tailWord_1526990).sum := by decide
  have hdescent : baseEnd_1526990 < baseStart_1526990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527023 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_1527023 : Nat := 118140960795 + 1527023 * 2 ^ 59
def prefixEnd_1527023 : Nat := 4983230072969 + 3 ^ 40 * 1527023 * 2
def baseEnd_1527023 : Nat := 784096769470684249189855

theorem tailTrace_1527023 : CollatzResearch.WordTrace tailWord_1527023 prefixEnd_1527023 784096769470684249189855 := by
  unfold tailWord_1527023
  simp only [CollatzResearch.WordTrace]
  refine ⟨55695104346863940610577723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37130069564575960407051815 55695104346863940610577723)
  ·
    refine ⟨83542656520295910915866585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55695104346863940610577723 83542656520295910915866585)
    ·
      refine ⟨62656992390221933186899939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83542656520295910915866585 62656992390221933186899939)
      ·
        refine ⟨93985488585332899780349909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62656992390221933186899939 93985488585332899780349909)
        ·
          refine ⟨2202784888718739838601951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93985488585332899780349909 2202784888718739838601951)
          ·
            refine ⟨3304177333078109757902927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202784888718739838601951 3304177333078109757902927)
            ·
              refine ⟨4956265999617164636854391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304177333078109757902927 4956265999617164636854391)
              ·
                refine ⟨7434398999425746955281587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956265999617164636854391 7434398999425746955281587)
                ·
                  refine ⟨11151598499138620432922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434398999425746955281587 11151598499138620432922381)
                  ·
                    refine ⟨4181849437176982662345893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11151598499138620432922381 4181849437176982662345893)
                    ·
                      refine ⟨784096769470684249189855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4181849437176982662345893 784096769470684249189855)
                      ·
                        rfl

theorem cell23_1527023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_1527023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527023 prefixEnd_1527023 := by exact prefixLift 1527023
  have htrace : WordTrace (prefixWord ++ tailWord_1527023) baseStart_1527023 baseEnd_1527023 := by
    simpa [prefixWord, tailWord_1527023, baseEnd_1527023] using wordTrace_append hprefix tailTrace_1527023
  have hstable : (prefixWord ++ tailWord_1527023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527023).length < 2 ^ (prefixWord ++ tailWord_1527023).sum := by decide
  have hdescent : baseEnd_1527023 < baseStart_1527023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527094 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1527094 : Nat := 118140960795 + 1527094 * 2 ^ 59
def prefixEnd_1527094 : Nat := 4983230072969 + 3 ^ 40 * 1527094 * 2
def baseEnd_1527094 : Nat := 784133226597153471402029

theorem tailTrace_1527094 : CollatzResearch.WordTrace tailWord_1527094 prefixEnd_1527094 784133226597153471402029 := by
  unfold tailWord_1527094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481105870600419983525771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37131795953071146490941557 3481105870600419983525771)
  ·
    refine ⟨5221658805900629975288657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481105870600419983525771 5221658805900629975288657)
    ·
      refine ⟨3916244104425472481466493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5221658805900629975288657 3916244104425472481466493)
      ·
        refine ⟨1468591539159552180549935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3916244104425472481466493 1468591539159552180549935)
        ·
          refine ⟨2202887308739328270824903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468591539159552180549935 2202887308739328270824903)
          ·
            refine ⟨3304330963108992406237355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202887308739328270824903 3304330963108992406237355)
            ·
              refine ⟨4956496444663488609356033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304330963108992406237355 4956496444663488609356033)
              ·
                refine ⟨3717372333497616457017025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956496444663488609356033 3717372333497616457017025)
                ·
                  refine ⟨2788029250123212342762769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717372333497616457017025 2788029250123212342762769)
                  ·
                    refine ⟨2091021937592409257072077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788029250123212342762769 2091021937592409257072077)
                    ·
                      refine ⟨784133226597153471402029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091021937592409257072077 784133226597153471402029)
                      ·
                        rfl

theorem cell23_1527094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1527094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527094 prefixEnd_1527094 := by exact prefixLift 1527094
  have htrace : WordTrace (prefixWord ++ tailWord_1527094) baseStart_1527094 baseEnd_1527094 := by
    simpa [prefixWord, tailWord_1527094, baseEnd_1527094] using wordTrace_append hprefix tailTrace_1527094
  have hstable : (prefixWord ++ tailWord_1527094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527094).length < 2 ^ (prefixWord ++ tailWord_1527094).sum := by decide
  have hdescent : baseEnd_1527094 < baseStart_1527094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527100 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_1527100 : Nat := 118140960795 + 1527100 * 2 ^ 59
def prefixEnd_1527100 : Nat := 4983230072969 + 3 ^ 40 * 1527100 * 2
def baseEnd_1527100 : Nat := 784136307481080447927001

theorem tailTrace_1527100 : CollatzResearch.WordTrace tailWord_1527100 prefixEnd_1527100 784136307481080447927001 := by
  unfold tailWord_1527100
  simp only [CollatzResearch.WordTrace]
  refine ⟨27848956383792491380565377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37131941845056655174087169 27848956383792491380565377)
  ·
    refine ⟨20886717287844368535424033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27848956383792491380565377 20886717287844368535424033)
    ·
      refine ⟨15665037965883276401568025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20886717287844368535424033 15665037965883276401568025)
      ·
        refine ⟨11748778474412457301176019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15665037965883276401568025 11748778474412457301176019)
        ·
          refine ⟨17623167711618685951764029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11748778474412457301176019 17623167711618685951764029)
          ·
            refine ⟨6608687891857007231911511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17623167711618685951764029 6608687891857007231911511)
            ·
              refine ⟨9913031837785510847867267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608687891857007231911511 9913031837785510847867267)
              ·
                refine ⟨14869547756678266271800901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9913031837785510847867267 14869547756678266271800901)
                ·
                  refine ⟨2788040204377174925962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14869547756678266271800901 2788040204377174925962669)
                  ·
                    refine ⟨1045515076641440597236001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2788040204377174925962669 1045515076641440597236001)
                    ·
                      refine ⟨784136307481080447927001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045515076641440597236001 784136307481080447927001)
                      ·
                        rfl

theorem cell23_1527100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_1527100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527100 prefixEnd_1527100 := by exact prefixLift 1527100
  have htrace : WordTrace (prefixWord ++ tailWord_1527100) baseStart_1527100 baseEnd_1527100 := by
    simpa [prefixWord, tailWord_1527100, baseEnd_1527100] using wordTrace_append hprefix tailTrace_1527100
  have hstable : (prefixWord ++ tailWord_1527100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527100).length < 2 ^ (prefixWord ++ tailWord_1527100).sum := by decide
  have hdescent : baseEnd_1527100 < baseStart_1527100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527101 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1527101 : Nat := 118140960795 + 1527101 * 2 ^ 59
def prefixEnd_1527101 : Nat := 4983230072969 + 3 ^ 40 * 1527101 * 2
def baseEnd_1527101 : Nat := 261378940320578314671499

theorem tailTrace_1527101 : CollatzResearch.WordTrace tailWord_1527101 prefixEnd_1527101 261378940320578314671499 := by
  unfold tailWord_1527101
  simp only [CollatzResearch.WordTrace]
  refine ⟨55697949240581359931917157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37131966160387573287944771 55697949240581359931917157)
  ·
    refine ⟨10443365482609004987234467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55697949240581359931917157 10443365482609004987234467)
    ·
      refine ⟨15665048223913507480851701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10443365482609004987234467 15665048223913507480851701)
      ·
        refine ⟨1468598270991891326329847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15665048223913507480851701 1468598270991891326329847)
        ·
          refine ⟨2202897406487836989494771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468598270991891326329847 2202897406487836989494771)
          ·
            refine ⟨3304346109731755484242157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202897406487836989494771 3304346109731755484242157)
            ·
              refine ⟨1239129791149408306590809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3304346109731755484242157 1239129791149408306590809)
              ·
                refine ⟨929347343362056229943107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239129791149408306590809 929347343362056229943107)
                ·
                  refine ⟨1394021015043084344914661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929347343362056229943107 1394021015043084344914661)
                  ·
                    refine ⟨261378940320578314671499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1394021015043084344914661 261378940320578314671499)
                    ·
                      rfl

theorem cell23_1527101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1527101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527101 prefixEnd_1527101 := by exact prefixLift 1527101
  have htrace : WordTrace (prefixWord ++ tailWord_1527101) baseStart_1527101 baseEnd_1527101 := by
    simpa [prefixWord, tailWord_1527101, baseEnd_1527101] using wordTrace_append hprefix tailTrace_1527101
  have hstable : (prefixWord ++ tailWord_1527101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527101).length < 2 ^ (prefixWord ++ tailWord_1527101).sum := by decide
  have hdescent : baseEnd_1527101 < baseStart_1527101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527130 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1527130 : Nat := 118140960795 + 1527130 * 2 ^ 59
def prefixEnd_1527130 : Nat := 4983230072969 + 3 ^ 40 * 1527130 * 2
def baseEnd_1527130 : Nat := 784151711900715330551863

theorem tailTrace_1527130 : CollatzResearch.WordTrace tailWord_1527130 prefixEnd_1527130 784151711900715330551863 := by
  unfold tailWord_1527130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924751739369074471180711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37132671304984198589815229 13924751739369074471180711)
  ·
    refine ⟨20887127609053611706771067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13924751739369074471180711 20887127609053611706771067)
    ·
      refine ⟨31330691413580417560156601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20887127609053611706771067 31330691413580417560156601)
      ·
        refine ⟨23498018560185313170117451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31330691413580417560156601 23498018560185313170117451)
        ·
          refine ⟨35247027840277969755176177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23498018560185313170117451 35247027840277969755176177)
          ·
            refine ⟨26435270880208477316382133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35247027840277969755176177 26435270880208477316382133)
            ·
              refine ⟨2478306645019544748410825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26435270880208477316382133 2478306645019544748410825)
              ·
                refine ⟨1858729983764658561308119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478306645019544748410825 1858729983764658561308119)
                ·
                  refine ⟨2788094975646987841962179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858729983764658561308119 2788094975646987841962179)
                  ·
                    refine ⟨4182142463470481762943269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788094975646987841962179 4182142463470481762943269)
                    ·
                      refine ⟨784151711900715330551863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4182142463470481762943269 784151711900715330551863)
                      ·
                        rfl

theorem cell23_1527130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1527130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527130 prefixEnd_1527130 := by exact prefixLift 1527130
  have htrace : WordTrace (prefixWord ++ tailWord_1527130) baseStart_1527130 baseEnd_1527130 := by
    simpa [prefixWord, tailWord_1527130, baseEnd_1527130] using wordTrace_append hprefix tailTrace_1527130
  have hstable : (prefixWord ++ tailWord_1527130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527130).length < 2 ^ (prefixWord ++ tailWord_1527130).sum := by decide
  have hdescent : baseEnd_1527130 < baseStart_1527130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527163 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3]
def baseStart_1527163 : Nat := 118140960795 + 1527163 * 2 ^ 59
def prefixEnd_1527163 : Nat := 4983230072969 + 3 ^ 40 * 1527163 * 2
def baseEnd_1527163 : Nat := 784168656762313701439211

theorem tailTrace_1527163 : CollatzResearch.WordTrace tailWord_1527163 prefixEnd_1527163 784168656762313701439211 := by
  unfold tailWord_1527163
  simp only [CollatzResearch.WordTrace]
  refine ⟨55700210566356744520674143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37133473710904496347116095 55700210566356744520674143)
  ·
    refine ⟨83550315849535116781011215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55700210566356744520674143 83550315849535116781011215)
    ·
      refine ⟨125325473774302675171516823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83550315849535116781011215 125325473774302675171516823)
      ·
        refine ⟨187988210661454012757275235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125325473774302675171516823 187988210661454012757275235)
        ·
          refine ⟨281982315992181019135912853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187988210661454012757275235 281982315992181019135912853)
          ·
            refine ⟨13217921062133485271995915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 281982315992181019135912853 13217921062133485271995915)
            ·
              refine ⟨19826881593200227907993873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13217921062133485271995915 19826881593200227907993873)
              ·
                refine ⟨14870161194900170930995405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19826881593200227907993873 14870161194900170930995405)
                ·
                  refine ⟨5576310448087564099123277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14870161194900170930995405 5576310448087564099123277)
                  ·
                    refine ⟨2091116418032836537171229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5576310448087564099123277 2091116418032836537171229)
                    ·
                      refine ⟨784168656762313701439211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091116418032836537171229 784168656762313701439211)
                      ·
                        rfl

theorem cell23_1527163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].length) (baseStart_1527163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527163 prefixEnd_1527163 := by exact prefixLift 1527163
  have htrace : WordTrace (prefixWord ++ tailWord_1527163) baseStart_1527163 baseEnd_1527163 := by
    simpa [prefixWord, tailWord_1527163, baseEnd_1527163] using wordTrace_append hprefix tailTrace_1527163
  have hstable : (prefixWord ++ tailWord_1527163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527163).length < 2 ^ (prefixWord ++ tailWord_1527163).sum := by decide
  have hdescent : baseEnd_1527163 < baseStart_1527163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527164 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_1527164 : Nat := 118140960795 + 1527164 * 2 ^ 59
def prefixEnd_1527164 : Nat := 4983230072969 + 3 ^ 40 * 1527164 * 2
def baseEnd_1527164 : Nat := 784169170242968197526707

theorem tailTrace_1527164 : CollatzResearch.WordTrace tailWord_1527164 prefixEnd_1527164 784169170242968197526707 := by
  unfold tailWord_1527164
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850123519676560845730273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37133498026235414460973697 27850123519676560845730273)
  ·
    refine ⟨20887592639757420634297705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27850123519676560845730273 20887592639757420634297705)
    ·
      refine ⟨15665694479818065475723279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20887592639757420634297705 15665694479818065475723279)
      ·
        refine ⟨23498541719727098213584919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15665694479818065475723279 23498541719727098213584919)
        ·
          refine ⟨35247812579590647320377379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23498541719727098213584919 35247812579590647320377379)
          ·
            refine ⟨52871718869385970980566069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35247812579590647320377379 52871718869385970980566069)
            ·
              refine ⟨4956723644004934779428069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52871718869385970980566069 4956723644004934779428069)
              ·
                refine ⟨929385683250925271142763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4956723644004934779428069 929385683250925271142763)
                ·
                  refine ⟨1394078524876387906714145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929385683250925271142763 1394078524876387906714145)
                  ·
                    refine ⟨1045558893657290930035609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394078524876387906714145 1045558893657290930035609)
                    ·
                      refine ⟨784169170242968197526707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045558893657290930035609 784169170242968197526707)
                      ·
                        rfl

theorem cell23_1527164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_1527164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527164 prefixEnd_1527164 := by exact prefixLift 1527164
  have htrace : WordTrace (prefixWord ++ tailWord_1527164) baseStart_1527164 baseEnd_1527164 := by
    simpa [prefixWord, tailWord_1527164, baseEnd_1527164] using wordTrace_append hprefix tailTrace_1527164
  have hstable : (prefixWord ++ tailWord_1527164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527164).length < 2 ^ (prefixWord ++ tailWord_1527164).sum := by decide
  have hdescent : baseEnd_1527164 < baseStart_1527164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527180 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1527180 : Nat := 118140960795 + 1527180 * 2 ^ 59
def prefixEnd_1527180 : Nat := 4983230072969 + 3 ^ 40 * 1527180 * 2
def baseEnd_1527180 : Nat := 784177385933440134926633

theorem tailTrace_1527180 : CollatzResearch.WordTrace tailWord_1527180 prefixEnd_1527180 784177385933440134926633 := by
  unfold tailWord_1527180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850415303647578212021497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37133887071530104282695329 27850415303647578212021497)
  ·
    refine ⟨20887811477735683659016123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27850415303647578212021497 20887811477735683659016123)
    ·
      refine ⟨31331717216603525488524185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20887811477735683659016123 31331717216603525488524185)
      ·
        refine ⟨23498787912452644116393139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31331717216603525488524185 23498787912452644116393139)
        ·
          refine ⟨35248181868678966174589709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23498787912452644116393139 35248181868678966174589709)
          ·
            refine ⟨13218068200754612315471141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35248181868678966174589709 13218068200754612315471141)
            ·
              refine ⟨2478387787641489809150839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13218068200754612315471141 2478387787641489809150839)
              ·
                refine ⟨3717581681462234713726259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478387787641489809150839 3717581681462234713726259)
                ·
                  refine ⟨5576372522193352070589389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717581681462234713726259 5576372522193352070589389)
                  ·
                    refine ⟨2091139695822507026471021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5576372522193352070589389 2091139695822507026471021)
                    ·
                      refine ⟨784177385933440134926633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091139695822507026471021 784177385933440134926633)
                      ·
                        rfl

theorem cell23_1527180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1527180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527180 prefixEnd_1527180 := by exact prefixLift 1527180
  have htrace : WordTrace (prefixWord ++ tailWord_1527180) baseStart_1527180 baseEnd_1527180 := by
    simpa [prefixWord, tailWord_1527180, baseEnd_1527180] using wordTrace_append hprefix tailTrace_1527180
  have hstable : (prefixWord ++ tailWord_1527180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527180).length < 2 ^ (prefixWord ++ tailWord_1527180).sum := by decide
  have hdescent : baseEnd_1527180 < baseStart_1527180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527198 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1527198 : Nat := 118140960795 + 1527198 * 2 ^ 59
def prefixEnd_1527198 : Nat := 4983230072969 + 3 ^ 40 * 1527198 * 2
def baseEnd_1527198 : Nat := 784186628585221064501551

theorem tailTrace_1527198 : CollatzResearch.WordTrace tailWord_1527198 prefixEnd_1527198 784186628585221064501551 := by
  unfold tailWord_1527198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962685890153743187274781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37134324747486630332132165 6962685890153743187274781)
  ·
    refine ⟨2611007208807653695228043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6962685890153743187274781 2611007208807653695228043)
    ·
      refine ⟨3916510813211480542842065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611007208807653695228043 3916510813211480542842065)
      ·
        refine ⟨2937383109908610407131549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3916510813211480542842065 2937383109908610407131549)
        ·
          refine ⟨1101518666215728902674331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2937383109908610407131549 1101518666215728902674331)
          ·
            refine ⟨1652277999323593354011497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101518666215728902674331 1652277999323593354011497)
            ·
              refine ⟨1239208499492695015508623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652277999323593354011497 1239208499492695015508623)
              ·
                refine ⟨1858812749239042523262935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239208499492695015508623 1858812749239042523262935)
                ·
                  refine ⟨2788219123858563784894403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858812749239042523262935 2788219123858563784894403)
                  ·
                    refine ⟨4182328685787845677341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788219123858563784894403 4182328685787845677341605)
                    ·
                      refine ⟨784186628585221064501551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4182328685787845677341605 784186628585221064501551)
                      ·
                        rfl

theorem cell23_1527198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1527198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527198 prefixEnd_1527198 := by exact prefixLift 1527198
  have htrace : WordTrace (prefixWord ++ tailWord_1527198) baseStart_1527198 baseEnd_1527198 := by
    simpa [prefixWord, tailWord_1527198, baseEnd_1527198] using wordTrace_append hprefix tailTrace_1527198
  have hstable : (prefixWord ++ tailWord_1527198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527198).length < 2 ^ (prefixWord ++ tailWord_1527198).sum := by decide
  have hdescent : baseEnd_1527198 < baseStart_1527198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527243 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 7]
def baseStart_1527243 : Nat := 118140960795 + 1527243 * 2 ^ 59
def prefixEnd_1527243 : Nat := 4983230072969 + 3 ^ 40 * 1527243 * 2
def baseEnd_1527243 : Nat := 87134415023852598715427

theorem tailTrace_1527243 : CollatzResearch.WordTrace tailWord_1527243 prefixEnd_1527243 87134415023852598715427 := by
  unfold tailWord_1527243
  simp only [CollatzResearch.WordTrace]
  refine ⟨55703128406066918183586383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37135418937377945455724255 55703128406066918183586383)
  ·
    refine ⟨83554692609100377275379575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55703128406066918183586383 83554692609100377275379575)
    ·
      refine ⟨125332038913650565913069363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83554692609100377275379575 125332038913650565913069363)
      ·
        refine ⟨187998058370475848869604045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125332038913650565913069363 187998058370475848869604045)
        ·
          refine ⟨70499271888928443326101517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187998058370475848869604045 70499271888928443326101517)
          ·
            refine ⟨26437226958348166247288069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70499271888928443326101517 26437226958348166247288069)
            ·
              refine ⟨4956980054690281171366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26437226958348166247288069 4956980054690281171366513)
              ·
                refine ⟨3717735041017710878524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956980054690281171366513 3717735041017710878524885)
                ·
                  refine ⟨87134415023852598715427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3717735041017710878524885 87134415023852598715427)
                  ·
                    rfl

theorem cell23_1527243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 7].length) (baseStart_1527243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527243 prefixEnd_1527243 := by exact prefixLift 1527243
  have htrace : WordTrace (prefixWord ++ tailWord_1527243) baseStart_1527243 baseEnd_1527243 := by
    simpa [prefixWord, tailWord_1527243, baseEnd_1527243] using wordTrace_append hprefix tailTrace_1527243
  have hstable : (prefixWord ++ tailWord_1527243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527243).length < 2 ^ (prefixWord ++ tailWord_1527243).sum := by decide
  have hdescent : baseEnd_1527243 < baseStart_1527243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527307 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 2, 5]
def baseStart_1527307 : Nat := 118140960795 + 1527307 * 2 ^ 59
def prefixEnd_1527307 : Nat := 4983230072969 + 3 ^ 40 * 1527307 * 2
def baseEnd_1527307 : Nat := 261414199325520379346183

theorem tailTrace_1527307 : CollatzResearch.WordTrace tailWord_1527307 prefixEnd_1527307 261414199325520379346183 := by
  unfold tailWord_1527307
  simp only [CollatzResearch.WordTrace]
  refine ⟨55705462677835057113916175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37136975118556704742610783 55705462677835057113916175)
  ·
    refine ⟨83558194016752585670874263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55705462677835057113916175 83558194016752585670874263)
    ·
      refine ⟨125337291025128878506311395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83558194016752585670874263 125337291025128878506311395)
      ·
        refine ⟨188005936537693317759467093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125337291025128878506311395 188005936537693317759467093)
        ·
          refine ⟨2203194568801093567493755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 188005936537693317759467093 2203194568801093567493755)
          ·
            refine ⟨3304791853201640351240633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203194568801093567493755 3304791853201640351240633)
            ·
              refine ⟨2478593889901230263430475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304791853201640351240633 2478593889901230263430475)
              ·
                refine ⟨3717890834851845395145713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478593889901230263430475 3717890834851845395145713)
                ·
                  refine ⟨2788418126138884046359285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717890834851845395145713 2788418126138884046359285)
                  ·
                    refine ⟨261414199325520379346183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2788418126138884046359285 261414199325520379346183)
                    ·
                      rfl

theorem cell23_1527307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].length) (baseStart_1527307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527307 prefixEnd_1527307 := by exact prefixLift 1527307
  have htrace : WordTrace (prefixWord ++ tailWord_1527307) baseStart_1527307 baseEnd_1527307 := by
    simpa [prefixWord, tailWord_1527307, baseEnd_1527307] using wordTrace_append hprefix tailTrace_1527307
  have hstable : (prefixWord ++ tailWord_1527307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527307).length < 2 ^ (prefixWord ++ tailWord_1527307).sum := by decide
  have hdescent : baseEnd_1527307 < baseStart_1527307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527377 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_1527377 : Nat := 118140960795 + 1527377 * 2 ^ 59
def prefixEnd_1527377 : Nat := 4983230072969 + 3 ^ 40 * 1527377 * 2
def baseEnd_1527377 : Nat := 784278541622375864163227

theorem tailTrace_1527377 : CollatzResearch.WordTrace tailWord_1527377 prefixEnd_1527377 784278541622375864163227 := by
  unfold tailWord_1527377
  simp only [CollatzResearch.WordTrace]
  refine ⟨55708015787581459068964385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37138677191720972712642923 55708015787581459068964385)
  ·
    refine ⟨41781011840686094301723289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55708015787581459068964385 41781011840686094301723289)
    ·
      refine ⟨31335758880514570726292467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41781011840686094301723289 31335758880514570726292467)
      ·
        refine ⟨47003638320771856089438701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31335758880514570726292467 47003638320771856089438701)
        ·
          refine ⟨17626364370289446033539513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47003638320771856089438701 17626364370289446033539513)
          ·
            refine ⟨13219773277717084525154635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17626364370289446033539513 13219773277717084525154635)
            ·
              refine ⟨19829659916575626787731953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13219773277717084525154635 19829659916575626787731953)
              ·
                refine ⟨14872244937431720090798965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19829659916575626787731953 14872244937431720090798965)
                ·
                  refine ⟨1394272962884223758512403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14872244937431720090798965 1394272962884223758512403)
                  ·
                    refine ⟨2091409444326335637768605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394272962884223758512403 2091409444326335637768605)
                    ·
                      refine ⟨784278541622375864163227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091409444326335637768605 784278541622375864163227)
                      ·
                        rfl

theorem cell23_1527377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_1527377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527377 prefixEnd_1527377 := by exact prefixLift 1527377
  have htrace : WordTrace (prefixWord ++ tailWord_1527377) baseStart_1527377 baseEnd_1527377 := by
    simpa [prefixWord, tailWord_1527377, baseEnd_1527377] using wordTrace_append hprefix tailTrace_1527377
  have hstable : (prefixWord ++ tailWord_1527377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527377).length < 2 ^ (prefixWord ++ tailWord_1527377).sum := by decide
  have hdescent : baseEnd_1527377 < baseStart_1527377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527414 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1527414 : Nat := 118140960795 + 1527414 * 2 ^ 59
def prefixEnd_1527414 : Nat := 4983230072969 + 3 ^ 40 * 1527414 * 2
def baseEnd_1527414 : Nat := 261432513468864073133519

theorem tailTrace_1527414 : CollatzResearch.WordTrace tailWord_1527414 prefixEnd_1527414 261432513468864073133519 := by
  unfold tailWord_1527414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481835330527963399253831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37139576858964942925374197 3481835330527963399253831)
  ·
    refine ⟨5222752995791945098880747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481835330527963399253831 5222752995791945098880747)
    ·
      refine ⟨7834129493687917648321121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222752995791945098880747 7834129493687917648321121)
      ·
        refine ⟨5875597120265938236240841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7834129493687917648321121 5875597120265938236240841)
        ·
          refine ⟨4406697840199453677180631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5875597120265938236240841 4406697840199453677180631)
          ·
            refine ⟨6610046760299180515770947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406697840199453677180631 6610046760299180515770947)
            ·
              refine ⟨9915070140448770773656421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610046760299180515770947 9915070140448770773656421)
              ·
                refine ⟨1859075651334144520060579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9915070140448770773656421 1859075651334144520060579)
                ·
                  refine ⟨2788613477001216780090869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859075651334144520060579 2788613477001216780090869)
                  ·
                    refine ⟨261432513468864073133519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2788613477001216780090869 261432513468864073133519)
                    ·
                      rfl

theorem cell23_1527414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1527414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527414 prefixEnd_1527414 := by exact prefixLift 1527414
  have htrace : WordTrace (prefixWord ++ tailWord_1527414) baseStart_1527414 baseEnd_1527414 := by
    simpa [prefixWord, tailWord_1527414, baseEnd_1527414] using wordTrace_append hprefix tailTrace_1527414
  have hstable : (prefixWord ++ tailWord_1527414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527414).length < 2 ^ (prefixWord ++ tailWord_1527414).sum := by decide
  have hdescent : baseEnd_1527414 < baseStart_1527414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527417 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1527417 : Nat := 118140960795 + 1527417 * 2 ^ 59
def prefixEnd_1527417 : Nat := 4983230072969 + 3 ^ 40 * 1527417 * 2
def baseEnd_1527417 : Nat := 784299080848555707663043

theorem tailTrace_1527417 : CollatzResearch.WordTrace tailWord_1527417 prefixEnd_1527417 784299080848555707663043 := by
  unfold tailWord_1527417
  simp only [CollatzResearch.WordTrace]
  refine ⟨55709474707436545900420505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37139649804957697266947003 55709474707436545900420505)
  ·
    refine ⟨41782106030577409425315379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55709474707436545900420505 41782106030577409425315379)
    ·
      refine ⟨62673159045866114137973069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41782106030577409425315379 62673159045866114137973069)
      ·
        refine ⟨23502434642199792801739901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62673159045866114137973069 23502434642199792801739901)
        ·
          refine ⟨8813412990824922300652463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23502434642199792801739901 8813412990824922300652463)
          ·
            refine ⟨13220119486237383450978695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813412990824922300652463 13220119486237383450978695)
            ·
              refine ⟨19830179229356075176468043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13220119486237383450978695 19830179229356075176468043)
              ·
                refine ⟨29745268844034112764702065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19830179229356075176468043 29745268844034112764702065)
                ·
                  refine ⟨22308951633025584573526549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29745268844034112764702065 22308951633025584573526549)
                  ·
                    refine ⟨1045732107798074276884057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22308951633025584573526549 1045732107798074276884057)
                    ·
                      refine ⟨784299080848555707663043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045732107798074276884057 784299080848555707663043)
                      ·
                        rfl

theorem cell23_1527417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1527417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527417 prefixEnd_1527417 := by exact prefixLift 1527417
  have htrace : WordTrace (prefixWord ++ tailWord_1527417) baseStart_1527417 baseEnd_1527417 := by
    simpa [prefixWord, tailWord_1527417, baseEnd_1527417] using wordTrace_append hprefix tailTrace_1527417
  have hstable : (prefixWord ++ tailWord_1527417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527417).length < 2 ^ (prefixWord ++ tailWord_1527417).sum := by decide
  have hdescent : baseEnd_1527417 < baseStart_1527417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527420 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1527420 : Nat := 118140960795 + 1527420 * 2 ^ 59
def prefixEnd_1527420 : Nat := 4983230072969 + 3 ^ 40 * 1527420 * 2
def baseEnd_1527420 : Nat := 784300621290519195925529

theorem tailTrace_1527420 : CollatzResearch.WordTrace tailWord_1527420 prefixEnd_1527420 784300621290519195925529 := by
  unfold tailWord_1527420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27854792063212838706389857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37139722750950451608519809 27854792063212838706389857)
  ·
    refine ⟨20891094047409629029792393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27854792063212838706389857 20891094047409629029792393)
    ·
      refine ⟨15668320535557221772344295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20891094047409629029792393 15668320535557221772344295)
      ·
        refine ⟨23502480803335832658516443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15668320535557221772344295 23502480803335832658516443)
        ·
          refine ⟨35253721205003748987774665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23502480803335832658516443 35253721205003748987774665)
          ·
            refine ⟨26440290903752811740830999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35253721205003748987774665 26440290903752811740830999)
            ·
              refine ⟨39660436355629217611246499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26440290903752811740830999 39660436355629217611246499)
              ·
                refine ⟨59490654533443826416869749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39660436355629217611246499 59490654533443826416869749)
                ·
                  refine ⟨5577248862510358726581539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59490654533443826416869749 5577248862510358726581539)
                  ·
                    refine ⟨8365873293765538089872309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577248862510358726581539 8365873293765538089872309)
                    ·
                      refine ⟨784300621290519195925529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8365873293765538089872309 784300621290519195925529)
                      ·
                        rfl

theorem cell23_1527420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1527420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527420 prefixEnd_1527420 := by exact prefixLift 1527420
  have htrace : WordTrace (prefixWord ++ tailWord_1527420) baseStart_1527420 baseEnd_1527420 := by
    simpa [prefixWord, tailWord_1527420, baseEnd_1527420] using wordTrace_append hprefix tailTrace_1527420
  have hstable : (prefixWord ++ tailWord_1527420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527420).length < 2 ^ (prefixWord ++ tailWord_1527420).sum := by decide
  have hdescent : baseEnd_1527420 < baseStart_1527420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527434 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1527434 : Nat := 118140960795 + 1527434 * 2 ^ 59
def prefixEnd_1527434 : Nat := 4983230072969 + 3 ^ 40 * 1527434 * 2
def baseEnd_1527434 : Nat := 784307810019682141150465

theorem tailTrace_1527434 : CollatzResearch.WordTrace tailWord_1527434 prefixEnd_1527434 784307810019682141150465 := by
  unfold tailWord_1527434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13927523687093739450947339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37140063165583305202526237 13927523687093739450947339)
  ·
    refine ⟨20891285530640609176421009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13927523687093739450947339 20891285530640609176421009)
    ·
      refine ⟨15668464147980456882315757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20891285530640609176421009 15668464147980456882315757)
      ·
        refine ⟨5875674055492671330868409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15668464147980456882315757 5875674055492671330868409)
        ·
          refine ⟨4406755541619503498151307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5875674055492671330868409 4406755541619503498151307)
          ·
            refine ⟨6610133312429255247226961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406755541619503498151307 6610133312429255247226961)
            ·
              refine ⟨4957599984321941435420221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6610133312429255247226961 4957599984321941435420221)
              ·
                refine ⟨1859099994120728038282583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4957599984321941435420221 1859099994120728038282583)
                ·
                  refine ⟨2788649991181092057423875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859099994120728038282583 2788649991181092057423875)
                  ·
                    refine ⟨4182974986771638086135813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788649991181092057423875 4182974986771638086135813)
                    ·
                      refine ⟨784307810019682141150465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4182974986771638086135813 784307810019682141150465)
                      ·
                        rfl

theorem cell23_1527434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1527434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527434 prefixEnd_1527434 := by exact prefixLift 1527434
  have htrace : WordTrace (prefixWord ++ tailWord_1527434) baseStart_1527434 baseEnd_1527434 := by
    simpa [prefixWord, tailWord_1527434, baseEnd_1527434] using wordTrace_append hprefix tailTrace_1527434
  have hstable : (prefixWord ++ tailWord_1527434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527434).length < 2 ^ (prefixWord ++ tailWord_1527434).sum := by decide
  have hdescent : baseEnd_1527434 < baseStart_1527434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527454 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1527454 : Nat := 118140960795 + 1527454 * 2 ^ 59
def prefixEnd_1527454 : Nat := 4983230072969 + 3 ^ 40 * 1527454 * 2
def baseEnd_1527454 : Nat := 784318079632772062900373

theorem tailTrace_1527454 : CollatzResearch.WordTrace tailWord_1527454 prefixEnd_1527454 784318079632772062900373 := by
  unfold tailWord_1527454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963853026037812652439677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37140549472201667479678277 6963853026037812652439677)
  ·
    refine ⟨2611444884764179744664879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6963853026037812652439677 2611444884764179744664879)
    ·
      refine ⟨3917167327146269616997319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611444884764179744664879 3917167327146269616997319)
      ·
        refine ⟨5875750990719404425495979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917167327146269616997319 5875750990719404425495979)
        ·
          refine ⟨8813626486079106638243969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875750990719404425495979 8813626486079106638243969)
          ·
            refine ⟨6610219864559329978682977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8813626486079106638243969 6610219864559329978682977)
            ·
              refine ⟨4957664898419497484012233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6610219864559329978682977 4957664898419497484012233)
              ·
                refine ⟨3718248673814623113009175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957664898419497484012233 3718248673814623113009175)
                ·
                  refine ⟨5577373010721934669513763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718248673814623113009175 5577373010721934669513763)
                  ·
                    refine ⟨8366059516082902004270645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577373010721934669513763 8366059516082902004270645)
                    ·
                      refine ⟨784318079632772062900373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8366059516082902004270645 784318079632772062900373)
                      ·
                        rfl

theorem cell23_1527454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1527454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527454 prefixEnd_1527454 := by exact prefixLift 1527454
  have htrace : WordTrace (prefixWord ++ tailWord_1527454) baseStart_1527454 baseEnd_1527454 := by
    simpa [prefixWord, tailWord_1527454, baseEnd_1527454] using wordTrace_append hprefix tailTrace_1527454
  have hstable : (prefixWord ++ tailWord_1527454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527454).length < 2 ^ (prefixWord ++ tailWord_1527454).sum := by decide
  have hdescent : baseEnd_1527454 < baseStart_1527454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527457 : List Nat := [1, 2, 3, 3, 2, 2, 2, 8]
def baseStart_1527457 : Nat := 118140960795 + 1527457 * 2 ^ 59
def prefixEnd_1527457 : Nat := 4983230072969 + 3 ^ 40 * 1527457 * 2
def baseEnd_1527457 : Nat := 29048874817582798191217

theorem tailTrace_1527457 : CollatzResearch.WordTrace tailWord_1527457 prefixEnd_1527457 29048874817582798191217 := by
  unfold tailWord_1527457
  simp only [CollatzResearch.WordTrace]
  refine ⟨55710933627291632731876625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37140622418194421821251083 55710933627291632731876625)
  ·
    refine ⟨41783200220468724548907469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55710933627291632731876625 41783200220468724548907469)
    ·
      refine ⟨15668700082675771705840301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41783200220468724548907469 15668700082675771705840301)
      ·
        refine ⟨5875762531003414389690113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15668700082675771705840301 5875762531003414389690113)
        ·
          refine ⟨4406821898252560792267585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5875762531003414389690113 4406821898252560792267585)
          ·
            refine ⟨3305116423689420594200689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4406821898252560792267585 3305116423689420594200689)
            ·
              refine ⟨2478837317767065445650517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305116423689420594200689 2478837317767065445650517)
              ·
                refine ⟨29048874817582798191217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2478837317767065445650517 29048874817582798191217)
                ·
                  rfl

theorem cell23_1527457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 8].length) (baseStart_1527457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527457 prefixEnd_1527457 := by exact prefixLift 1527457
  have htrace : WordTrace (prefixWord ++ tailWord_1527457) baseStart_1527457 baseEnd_1527457 := by
    simpa [prefixWord, tailWord_1527457, baseEnd_1527457] using wordTrace_append hprefix tailTrace_1527457
  have hstable : (prefixWord ++ tailWord_1527457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527457).length < 2 ^ (prefixWord ++ tailWord_1527457).sum := by decide
  have hdescent : baseEnd_1527457 < baseStart_1527457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527480 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1527480 : Nat := 118140960795 + 1527480 * 2 ^ 59
def prefixEnd_1527480 : Nat := 4983230072969 + 3 ^ 40 * 1527480 * 2
def baseEnd_1527480 : Nat := 784331430129788961175253

theorem tailTrace_1527480 : CollatzResearch.WordTrace tailWord_1527480 prefixEnd_1527480 784331430129788961175253 := by
  unfold tailWord_1527480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855886253104153829981947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37141181670805538439975929 27855886253104153829981947)
  ·
    refine ⟨41783829379656230744972921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27855886253104153829981947 41783829379656230744972921)
    ·
      refine ⟨31337872034742173058729691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41783829379656230744972921 31337872034742173058729691)
      ·
        refine ⟨47006808052113259588094537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31337872034742173058729691 47006808052113259588094537)
        ·
          refine ⟨35255106039084944691070903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47006808052113259588094537 35255106039084944691070903)
          ·
            refine ⟨52882659058627417036606355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35255106039084944691070903 52882659058627417036606355)
            ·
              refine ⟨79323988587941125554909533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52882659058627417036606355 79323988587941125554909533)
              ·
                refine ⟨29746495720477922083091075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79323988587941125554909533 29746495720477922083091075)
                ·
                  refine ⟨44619743580716883124636613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29746495720477922083091075 44619743580716883124636613)
                  ·
                    refine ⟨8366201921384415585869365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44619743580716883124636613 8366201921384415585869365)
                    ·
                      refine ⟨784331430129788961175253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8366201921384415585869365 784331430129788961175253)
                      ·
                        rfl

theorem cell23_1527480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1527480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527480 prefixEnd_1527480 := by exact prefixLift 1527480
  have htrace : WordTrace (prefixWord ++ tailWord_1527480) baseStart_1527480 baseEnd_1527480 := by
    simpa [prefixWord, tailWord_1527480, baseEnd_1527480] using wordTrace_append hprefix tailTrace_1527480
  have hstable : (prefixWord ++ tailWord_1527480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527480).length < 2 ^ (prefixWord ++ tailWord_1527480).sum := by decide
  have hdescent : baseEnd_1527480 < baseStart_1527480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527484 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1527484 : Nat := 118140960795 + 1527484 * 2 ^ 59
def prefixEnd_1527484 : Nat := 4983230072969 + 3 ^ 40 * 1527484 * 2
def baseEnd_1527484 : Nat := 784333484052406945525235

theorem tailTrace_1527484 : CollatzResearch.WordTrace tailWord_1527484 prefixEnd_1527484 784333484052406945525235 := by
  unfold tailWord_1527484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855959199096908171554753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37141278932129210895406337 27855959199096908171554753)
  ·
    refine ⟨20891969399322681128666065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27855959199096908171554753 20891969399322681128666065)
    ·
      refine ⟨15668977049492010846499549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20891969399322681128666065 15668977049492010846499549)
      ·
        refine ⟨5875866393559504067437331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15668977049492010846499549 5875866393559504067437331)
        ·
          refine ⟨8813799590339256101155997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875866393559504067437331 8813799590339256101155997)
          ·
            refine ⟨3305174846377221037933499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8813799590339256101155997 3305174846377221037933499)
            ·
              refine ⟨4957762269565831556900249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305174846377221037933499 4957762269565831556900249)
              ·
                refine ⟨3718321702174373667675187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957762269565831556900249 3718321702174373667675187)
                ·
                  refine ⟨5577482553261560501512781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718321702174373667675187 5577482553261560501512781)
                  ·
                    refine ⟨2091555957473085188067293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5577482553261560501512781 2091555957473085188067293)
                    ·
                      refine ⟨784333484052406945525235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091555957473085188067293 784333484052406945525235)
                      ·
                        rfl

theorem cell23_1527484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1527484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527484 prefixEnd_1527484 := by exact prefixLift 1527484
  have htrace : WordTrace (prefixWord ++ tailWord_1527484) baseStart_1527484 baseEnd_1527484 := by
    simpa [prefixWord, tailWord_1527484, baseEnd_1527484] using wordTrace_append hprefix tailTrace_1527484
  have hstable : (prefixWord ++ tailWord_1527484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527484).length < 2 ^ (prefixWord ++ tailWord_1527484).sum := by decide
  have hdescent : baseEnd_1527484 < baseStart_1527484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527554 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1527554 : Nat := 118140960795 + 1527554 * 2 ^ 59
def prefixEnd_1527554 : Nat := 4983230072969 + 3 ^ 40 * 1527554 * 2
def baseEnd_1527554 : Nat := 784369427698221671649913

theorem tailTrace_1527554 : CollatzResearch.WordTrace tailWord_1527554 prefixEnd_1527554 784369427698221671649913 := by
  unfold tailWord_1527554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928617876985054574539429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37142981005293478865438477 13928617876985054574539429)
  ·
    refine ⟨2611615851934697732726143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13928617876985054574539429 2611615851934697732726143)
    ·
      refine ⟨3917423777902046599089215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611615851934697732726143 3917423777902046599089215)
      ·
        refine ⟨5876135666853069898633823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917423777902046599089215 5876135666853069898633823)
        ·
          refine ⟨8814203500279604847950735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5876135666853069898633823 8814203500279604847950735)
          ·
            refine ⟨13221305250419407271926103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8814203500279604847950735 13221305250419407271926103)
            ·
              refine ⟨19831957875629110907889155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13221305250419407271926103 19831957875629110907889155)
              ·
                refine ⟨29747936813443666361833733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19831957875629110907889155 29747936813443666361833733)
                ·
                  refine ⟨5577738152520687442843825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29747936813443666361833733 5577738152520687442843825)
                  ·
                    refine ⟨4183303614390515582132869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5577738152520687442843825 4183303614390515582132869)
                    ·
                      refine ⟨784369427698221671649913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4183303614390515582132869 784369427698221671649913)
                      ·
                        rfl

theorem cell23_1527554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1527554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527554 prefixEnd_1527554 := by exact prefixLift 1527554
  have htrace : WordTrace (prefixWord ++ tailWord_1527554) baseStart_1527554 baseEnd_1527554 := by
    simpa [prefixWord, tailWord_1527554, baseEnd_1527554] using wordTrace_append hprefix tailTrace_1527554
  have hstable : (prefixWord ++ tailWord_1527554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527554).length < 2 ^ (prefixWord ++ tailWord_1527554).sum := by decide
  have hdescent : baseEnd_1527554 < baseStart_1527554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527564 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 5]
def baseStart_1527564 : Nat := 118140960795 + 1527564 * 2 ^ 59
def prefixEnd_1527564 : Nat := 4983230072969 + 3 ^ 40 * 1527564 * 2
def baseEnd_1527564 : Nat := 87152729167196292502763

theorem tailTrace_1527564 : CollatzResearch.WordTrace tailWord_1527564 prefixEnd_1527564 87152729167196292502763 := by
  unfold tailWord_1527564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27857418118951995003010873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37143224158602660004014497 27857418118951995003010873)
  ·
    refine ⟨20893063589213996252258155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27857418118951995003010873 20893063589213996252258155)
    ·
      refine ⟨31339595383820994378387233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20893063589213996252258155 31339595383820994378387233)
      ·
        refine ⟨23504696537865745783790425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31339595383820994378387233 23504696537865745783790425)
        ·
          refine ⟨17628522403399309337842819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23504696537865745783790425 17628522403399309337842819)
          ·
            refine ⟨26442783605098964006764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17628522403399309337842819 26442783605098964006764229)
            ·
              refine ⟨4958021925956055751268293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26442783605098964006764229 4958021925956055751268293)
              ·
                refine ⟨929629111116760453362805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4958021925956055751268293 929629111116760453362805)
                ·
                  refine ⟨87152729167196292502763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929629111116760453362805 87152729167196292502763)
                  ·
                    rfl

theorem cell23_1527564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_1527564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527564 prefixEnd_1527564 := by exact prefixLift 1527564
  have htrace : WordTrace (prefixWord ++ tailWord_1527564) baseStart_1527564 baseEnd_1527564 := by
    simpa [prefixWord, tailWord_1527564, baseEnd_1527564] using wordTrace_append hprefix tailTrace_1527564
  have hstable : (prefixWord ++ tailWord_1527564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527564).length < 2 ^ (prefixWord ++ tailWord_1527564).sum := by decide
  have hdescent : baseEnd_1527564 < baseStart_1527564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527575 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1527575 : Nat := 118140960795 + 1527575 * 2 ^ 59
def prefixEnd_1527575 : Nat := 4983230072969 + 3 ^ 40 * 1527575 * 2
def baseEnd_1527575 : Nat := 784380210791966089487317

theorem tailTrace_1527575 : CollatzResearch.WordTrace tailWord_1527575 prefixEnd_1527575 784380210791966089487317 := by
  unfold tailWord_1527575
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715237440864138884672179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37143491627242759256448119 55715237440864138884672179)
  ·
    refine ⟨83572856161296208327008269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55715237440864138884672179 83572856161296208327008269)
    ·
      refine ⟨31339821060486078122628101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83572856161296208327008269 31339821060486078122628101)
      ·
        refine ⟨5876216448841139647992769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31339821060486078122628101 5876216448841139647992769)
        ·
          refine ⟨4407162336630854735994577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876216448841139647992769 4407162336630854735994577)
          ·
            refine ⟨3305371752473141051995933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407162336630854735994577 3305371752473141051995933)
            ·
              refine ⟨1239514407177427894498475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305371752473141051995933 1239514407177427894498475)
              ·
                refine ⟨1859271610766141841747713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239514407177427894498475 1859271610766141841747713)
                ·
                  refine ⟨1394453708074606381310785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859271610766141841747713 1394453708074606381310785)
                  ·
                    refine ⟨1045840281055954785983089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394453708074606381310785 1045840281055954785983089)
                    ·
                      refine ⟨784380210791966089487317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045840281055954785983089 784380210791966089487317)
                      ·
                        rfl

theorem cell23_1527575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1527575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527575 prefixEnd_1527575 := by exact prefixLift 1527575
  have htrace : WordTrace (prefixWord ++ tailWord_1527575) baseStart_1527575 baseEnd_1527575 := by
    simpa [prefixWord, tailWord_1527575, baseEnd_1527575] using wordTrace_append hprefix tailTrace_1527575
  have hstable : (prefixWord ++ tailWord_1527575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527575).length < 2 ^ (prefixWord ++ tailWord_1527575).sum := by decide
  have hdescent : baseEnd_1527575 < baseStart_1527575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527684 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1527684 : Nat := 118140960795 + 1527684 * 2 ^ 59
def prefixEnd_1527684 : Nat := 4983230072969 + 3 ^ 40 * 1527684 * 2
def baseEnd_1527684 : Nat := 261478726727768721008105

theorem tailTrace_1527684 : CollatzResearch.WordTrace tailWord_1527684 prefixEnd_1527684 261478726727768721008105 := by
  unfold tailWord_1527684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27859606498734625250195053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37146141998312833666926737 27859606498734625250195053)
  ·
    refine ⟨10447352437025484468823145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27859606498734625250195053 10447352437025484468823145)
    ·
      refine ⟨7835514327769113351617359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10447352437025484468823145 7835514327769113351617359)
      ·
        refine ⟨11753271491653670027426039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835514327769113351617359 11753271491653670027426039)
        ·
          refine ⟨17629907237480505041139059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11753271491653670027426039 17629907237480505041139059)
          ·
            refine ⟨26444860856220757561708589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17629907237480505041139059 26444860856220757561708589)
            ·
              refine ⟨9916822821082784085640721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26444860856220757561708589 9916822821082784085640721)
              ·
                refine ⟨7437617115812088064230541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916822821082784085640721 7437617115812088064230541)
                ·
                  refine ⟨2789106418429533024086453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7437617115812088064230541 2789106418429533024086453)
                  ·
                    refine ⟨261478726727768721008105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2789106418429533024086453 261478726727768721008105)
                    ·
                      rfl

theorem cell23_1527684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1527684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527684 prefixEnd_1527684 := by exact prefixLift 1527684
  have htrace : WordTrace (prefixWord ++ tailWord_1527684) baseStart_1527684 baseEnd_1527684 := by
    simpa [prefixWord, tailWord_1527684, baseEnd_1527684] using wordTrace_append hprefix tailTrace_1527684
  have hstable : (prefixWord ++ tailWord_1527684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527684).length < 2 ^ (prefixWord ++ tailWord_1527684).sum := by decide
  have hdescent : baseEnd_1527684 < baseStart_1527684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527698 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1527698 : Nat := 118140960795 + 1527698 * 2 ^ 59
def prefixEnd_1527698 : Nat := 4983230072969 + 3 ^ 40 * 1527698 * 2
def baseEnd_1527698 : Nat := 784443368912469108249251

theorem tailTrace_1527698 : CollatzResearch.WordTrace tailWord_1527698 prefixEnd_1527698 784443368912469108249251 := by
  unfold tailWord_1527698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929930904854632722849937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37146482412945687260933165 13929930904854632722849937)
  ·
    refine ⟨10447448178640974542137453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13929930904854632722849937 10447448178640974542137453)
    ·
      refine ⟨3917793066990365453301545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10447448178640974542137453 3917793066990365453301545)
      ·
        refine ⟨2938344800242774089976159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917793066990365453301545 2938344800242774089976159)
        ·
          refine ⟨4407517200364161134964239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938344800242774089976159 4407517200364161134964239)
          ·
            refine ⟨6611275800546241702446359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407517200364161134964239 6611275800546241702446359)
            ·
              refine ⟨9916913700819362553669539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611275800546241702446359 9916913700819362553669539)
              ·
                refine ⟨14875370551229043830504309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9916913700819362553669539 14875370551229043830504309)
                ·
                  refine ⟨1394565989177722859109779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14875370551229043830504309 1394565989177722859109779)
                  ·
                    refine ⟨2091848983766584288664669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394565989177722859109779 2091848983766584288664669)
                    ·
                      refine ⟨784443368912469108249251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091848983766584288664669 784443368912469108249251)
                      ·
                        rfl

theorem cell23_1527698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1527698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527698 prefixEnd_1527698 := by exact prefixLift 1527698
  have htrace : WordTrace (prefixWord ++ tailWord_1527698) baseStart_1527698 baseEnd_1527698 := by
    simpa [prefixWord, tailWord_1527698, baseEnd_1527698] using wordTrace_append hprefix tailTrace_1527698
  have hstable : (prefixWord ++ tailWord_1527698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527698).length < 2 ^ (prefixWord ++ tailWord_1527698).sum := by decide
  have hdescent : baseEnd_1527698 < baseStart_1527698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527708 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1527708 : Nat := 118140960795 + 1527708 * 2 ^ 59
def prefixEnd_1527708 : Nat := 4983230072969 + 3 ^ 40 * 1527708 * 2
def baseEnd_1527708 : Nat := 784448503719014069124205

theorem tailTrace_1527708 : CollatzResearch.WordTrace tailWord_1527708 prefixEnd_1527708 784448503719014069124205 := by
  unfold tailWord_1527708
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860044174691151299631889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37146725566254868399509185 27860044174691151299631889)
  ·
    refine ⟨20895033131018363474723917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27860044174691151299631889 20895033131018363474723917)
    ·
      refine ⟨7835637424131886303021469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20895033131018363474723917 7835637424131886303021469)
      ·
        refine ⟨2938364034049457363633051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7835637424131886303021469 2938364034049457363633051)
        ·
          refine ⟨4407546051074186045449577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938364034049457363633051 4407546051074186045449577)
          ·
            refine ⟨3305659538305639534087183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407546051074186045449577 3305659538305639534087183)
            ·
              refine ⟨4958489307458459301130775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305659538305639534087183 4958489307458459301130775)
              ·
                refine ⟨7437733961187688951696163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958489307458459301130775 7437733961187688951696163)
                ·
                  refine ⟨11156600941781533427544245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437733961187688951696163 11156600941781533427544245)
                  ·
                    refine ⟨1045931338292018758832273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11156600941781533427544245 1045931338292018758832273)
                    ·
                      refine ⟨784448503719014069124205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045931338292018758832273 784448503719014069124205)
                      ·
                        rfl

theorem cell23_1527708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1527708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527708 prefixEnd_1527708 := by exact prefixLift 1527708
  have htrace : WordTrace (prefixWord ++ tailWord_1527708) baseStart_1527708 baseEnd_1527708 := by
    simpa [prefixWord, tailWord_1527708, baseEnd_1527708] using wordTrace_append hprefix tailTrace_1527708
  have hstable : (prefixWord ++ tailWord_1527708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527708).length < 2 ^ (prefixWord ++ tailWord_1527708).sum := by decide
  have hdescent : baseEnd_1527708 < baseStart_1527708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527727 : List Nat := [1, 1, 2, 1, 2, 2, 14]
def baseStart_1527727 : Nat := 118140960795 + 1527727 * 2 ^ 59
def prefixEnd_1527727 : Nat := 4983230072969 + 3 ^ 40 * 1527727 * 2
def baseEnd_1527727 : Nat := 9684669874709253022057

theorem tailTrace_1527727 : CollatzResearch.WordTrace tailWord_1527727 prefixEnd_1527727 9684669874709253022057 := by
  unfold tailWord_1527727
  simp only [CollatzResearch.WordTrace]
  refine ⟨55720781336313468844205435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37147187557542312562803623 55720781336313468844205435)
  ·
    refine ⟨83581172004470203266308153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55720781336313468844205435 83581172004470203266308153)
    ·
      refine ⟨62685879003352652449731115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83581172004470203266308153 62685879003352652449731115)
      ·
        refine ⟨94028818505028978674596673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62685879003352652449731115 94028818505028978674596673)
        ·
          refine ⟨70521613878771734005947505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94028818505028978674596673 70521613878771734005947505)
          ·
            refine ⟨52891210409078800504460629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70521613878771734005947505 52891210409078800504460629)
            ·
              refine ⟨9684669874709253022057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 52891210409078800504460629 9684669874709253022057)
              ·
                rfl

theorem cell23_1527727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 14].length) (baseStart_1527727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527727 prefixEnd_1527727 := by exact prefixLift 1527727
  have htrace : WordTrace (prefixWord ++ tailWord_1527727) baseStart_1527727 baseEnd_1527727 := by
    simpa [prefixWord, tailWord_1527727, baseEnd_1527727] using wordTrace_append hprefix tailTrace_1527727
  have hstable : (prefixWord ++ tailWord_1527727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527727).length < 2 ^ (prefixWord ++ tailWord_1527727).sum := by decide
  have hdescent : baseEnd_1527727 < baseStart_1527727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527732 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1527732 : Nat := 118140960795 + 1527732 * 2 ^ 59
def prefixEnd_1527732 : Nat := 4983230072969 + 3 ^ 40 * 1527732 * 2
def baseEnd_1527732 : Nat := 784460827254721975224095

theorem tailTrace_1527732 : CollatzResearch.WordTrace tailWord_1527732 prefixEnd_1527732 784460827254721975224095 := by
  unfold tailWord_1527732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860481850647677349068725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37147309134196903132091633 27860481850647677349068725)
  ·
    refine ⟨2611920173498219751475193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27860481850647677349068725 2611920173498219751475193)
    ·
      refine ⟨1958940130123664813606395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2611920173498219751475193 1958940130123664813606395)
      ·
        refine ⟨2938410195185497220409593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958940130123664813606395 2938410195185497220409593)
        ·
          refine ⟨2203807646389122915307195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938410195185497220409593 2203807646389122915307195)
          ·
            refine ⟨3305711469583684372960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203807646389122915307195 3305711469583684372960793)
            ·
              refine ⟨2479283602187763279720595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305711469583684372960793 2479283602187763279720595)
              ·
                refine ⟨3718925403281644919580893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479283602187763279720595 3718925403281644919580893)
                ·
                  refine ⟨1394597026230616844842835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3718925403281644919580893 1394597026230616844842835)
                  ·
                    refine ⟨2091895539345925267264253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394597026230616844842835 2091895539345925267264253)
                    ·
                      refine ⟨784460827254721975224095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091895539345925267264253 784460827254721975224095)
                      ·
                        rfl

theorem cell23_1527732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1527732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527732 prefixEnd_1527732 := by exact prefixLift 1527732
  have htrace : WordTrace (prefixWord ++ tailWord_1527732) baseStart_1527732 baseEnd_1527732 := by
    simpa [prefixWord, tailWord_1527732, baseEnd_1527732] using wordTrace_append hprefix tailTrace_1527732
  have hstable : (prefixWord ++ tailWord_1527732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527732).length < 2 ^ (prefixWord ++ tailWord_1527732).sum := by decide
  have hdescent : baseEnd_1527732 < baseStart_1527732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527741 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1527741 : Nat := 118140960795 + 1527741 * 2 ^ 59
def prefixEnd_1527741 : Nat := 4983230072969 + 3 ^ 40 * 1527741 * 2
def baseEnd_1527741 : Nat := 784465448580612440011553

theorem tailTrace_1527741 : CollatzResearch.WordTrace tailWord_1527741 prefixEnd_1527741 784465448580612440011553 := by
  unfold tailWord_1527741
  simp only [CollatzResearch.WordTrace]
  refine ⟨55721291958262749235215077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37147527972175166156810051 55721291958262749235215077)
  ·
    refine ⟨10447742242174265481602827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55721291958262749235215077 10447742242174265481602827)
    ·
      refine ⟨15671613363261398222404241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10447742242174265481602827 15671613363261398222404241)
      ·
        refine ⟨11753710022446048666803181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15671613363261398222404241 11753710022446048666803181)
        ·
          refine ⟨4407641258417268250051193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11753710022446048666803181 4407641258417268250051193)
          ·
            refine ⟨3305730943812951187538395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407641258417268250051193 3305730943812951187538395)
            ·
              refine ⟨4958596415719426781307593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305730943812951187538395 4958596415719426781307593)
              ·
                refine ⟨3718947311789570085980695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958596415719426781307593 3718947311789570085980695)
                ·
                  refine ⟨5578420967684355128971043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718947311789570085980695 5578420967684355128971043)
                  ·
                    refine ⟨8367631451526532693456565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5578420967684355128971043 8367631451526532693456565)
                    ·
                      refine ⟨784465448580612440011553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8367631451526532693456565 784465448580612440011553)
                      ·
                        rfl

theorem cell23_1527741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1527741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527741 prefixEnd_1527741 := by exact prefixLift 1527741
  have htrace : WordTrace (prefixWord ++ tailWord_1527741) baseStart_1527741 baseEnd_1527741 := by
    simpa [prefixWord, tailWord_1527741, baseEnd_1527741] using wordTrace_append hprefix tailTrace_1527741
  have hstable : (prefixWord ++ tailWord_1527741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527741).length < 2 ^ (prefixWord ++ tailWord_1527741).sum := by decide
  have hdescent : baseEnd_1527741 < baseStart_1527741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527758 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1527758 : Nat := 118140960795 + 1527758 * 2 ^ 59
def prefixEnd_1527758 : Nat := 4983230072969 + 3 ^ 40 * 1527758 * 2
def baseEnd_1527758 : Nat := 784474177751738873498975

theorem tailTrace_1527758 : CollatzResearch.WordTrace tailWord_1527758 prefixEnd_1527758 784474177751738873498975 := by
  unfold tailWord_1527758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965238999900145142322991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37147941332800774092389285 6965238999900145142322991)
  ·
    refine ⟨10447858499850217713484487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6965238999900145142322991 10447858499850217713484487)
    ·
      refine ⟨15671787749775326570226731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10447858499850217713484487 15671787749775326570226731)
      ·
        refine ⟨23507681624662989855340097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15671787749775326570226731 23507681624662989855340097)
        ·
          refine ⟨17630761218497242391505073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23507681624662989855340097 17630761218497242391505073)
          ·
            refine ⟨13223070913872931793628805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17630761218497242391505073 13223070913872931793628805)
            ·
              refine ⟨2479325796351174711305401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13223070913872931793628805 2479325796351174711305401)
              ·
                refine ⟨1859494347263381033479051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479325796351174711305401 1859494347263381033479051)
                ·
                  refine ⟨2789241520895071550218577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859494347263381033479051 2789241520895071550218577)
                  ·
                    refine ⟨2091931140671303662663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789241520895071550218577 2091931140671303662663933)
                    ·
                      refine ⟨784474177751738873498975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091931140671303662663933 784474177751738873498975)
                      ·
                        rfl

theorem cell23_1527758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1527758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527758 prefixEnd_1527758 := by exact prefixLift 1527758
  have htrace : WordTrace (prefixWord ++ tailWord_1527758) baseStart_1527758 baseEnd_1527758 := by
    simpa [prefixWord, tailWord_1527758, baseEnd_1527758] using wordTrace_append hprefix tailTrace_1527758
  have hstable : (prefixWord ++ tailWord_1527758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527758).length < 2 ^ (prefixWord ++ tailWord_1527758).sum := by decide
  have hdescent : baseEnd_1527758 < baseStart_1527758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527766 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1527766 : Nat := 118140960795 + 1527766 * 2 ^ 59
def prefixEnd_1527766 : Nat := 4983230072969 + 3 ^ 40 * 1527766 * 2
def baseEnd_1527766 : Nat := 784478285596974842198939

theorem tailTrace_1527766 : CollatzResearch.WordTrace tailWord_1527766 prefixEnd_1527766 784478285596974842198939 := by
  unfold tailWord_1527766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482637736448261156554697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37148135855448119003250101 3482637736448261156554697)
  ·
    refine ⟨2611978302336195867416023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3482637736448261156554697 2611978302336195867416023)
    ·
      refine ⟨3917967453504293801124035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611978302336195867416023 3917967453504293801124035)
      ·
        refine ⟨5876951180256440701686053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917967453504293801124035 5876951180256440701686053)
        ·
          refine ⟨1101928346298082631566135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5876951180256440701686053 1101928346298082631566135)
          ·
            refine ⟨1652892519447123947349203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101928346298082631566135 1652892519447123947349203)
            ·
              refine ⟨2479338779170685921023805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652892519447123947349203 2479338779170685921023805)
              ·
                refine ⟨929752042189007220383927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479338779170685921023805 929752042189007220383927)
                ·
                  refine ⟨1394628063283510830575891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929752042189007220383927 1394628063283510830575891)
                  ·
                    refine ⟨2091942094925266245863837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394628063283510830575891 2091942094925266245863837)
                    ·
                      refine ⟨784478285596974842198939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091942094925266245863837 784478285596974842198939)
                      ·
                        rfl

theorem cell23_1527766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1527766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527766 prefixEnd_1527766 := by exact prefixLift 1527766
  have htrace : WordTrace (prefixWord ++ tailWord_1527766) baseStart_1527766 baseEnd_1527766 := by
    simpa [prefixWord, tailWord_1527766, baseEnd_1527766] using wordTrace_append hprefix tailTrace_1527766
  have hstable : (prefixWord ++ tailWord_1527766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527766).length < 2 ^ (prefixWord ++ tailWord_1527766).sum := by decide
  have hdescent : baseEnd_1527766 < baseStart_1527766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527778 : List Nat := [3, 3, 3, 1, 2, 2, 9]
def baseStart_1527778 : Nat := 118140960795 + 1527778 * 2 ^ 59
def prefixEnd_1527778 : Nat := 4983230072969 + 3 ^ 40 * 1527778 * 2
def baseEnd_1527778 : Nat := 9684993177343565373443

theorem tailTrace_1527778 : CollatzResearch.WordTrace tailWord_1527778 prefixEnd_1527778 9684993177343565373443 := by
  unfold tailWord_1527778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930660364782176138577997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37148427639419136369541325 13930660364782176138577997)
  ·
    refine ⟨5223997636793316051966749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13930660364782176138577997 5223997636793316051966749)
    ·
      refine ⟨1958999113797493519487531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5223997636793316051966749 1958999113797493519487531)
      ·
        refine ⟨2938498670696240279231297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958999113797493519487531 2938498670696240279231297)
        ·
          refine ⟨2203874003022180209423473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938498670696240279231297 2203874003022180209423473)
          ·
            refine ⟨1652905502266635157067605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203874003022180209423473 1652905502266635157067605)
            ·
              refine ⟨9684993177343565373443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1652905502266635157067605 9684993177343565373443)
              ·
                rfl

theorem cell23_1527778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 9].length) (baseStart_1527778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527778 prefixEnd_1527778 := by exact prefixLift 1527778
  have htrace : WordTrace (prefixWord ++ tailWord_1527778) baseStart_1527778 baseEnd_1527778 := by
    simpa [prefixWord, tailWord_1527778, baseEnd_1527778] using wordTrace_append hprefix tailTrace_1527778
  have hstable : (prefixWord ++ tailWord_1527778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527778).length < 2 ^ (prefixWord ++ tailWord_1527778).sum := by decide
  have hdescent : baseEnd_1527778 < baseStart_1527778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527784 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1527784 : Nat := 118140960795 + 1527784 * 2 ^ 59
def prefixEnd_1527784 : Nat := 4983230072969 + 3 ^ 40 * 1527784 * 2
def baseEnd_1527784 : Nat := 784487528248755771773855

theorem tailTrace_1527784 : CollatzResearch.WordTrace tailWord_1527784 prefixEnd_1527784 784487528248755771773855 := by
  unfold tailWord_1527784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27861430148553483789515203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37148573531404645052686937 27861430148553483789515203)
  ·
    refine ⟨41792145222830225684272805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27861430148553483789515203 41792145222830225684272805)
    ·
      refine ⟨7836027229280667315801151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41792145222830225684272805 7836027229280667315801151)
      ·
        refine ⟨11754040843921000973701727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836027229280667315801151 11754040843921000973701727)
        ·
          refine ⟨17631061265881501460552591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754040843921000973701727 17631061265881501460552591)
          ·
            refine ⟨26446591898822252190828887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17631061265881501460552591 26446591898822252190828887)
            ·
              refine ⟨39669887848233378286243331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26446591898822252190828887 39669887848233378286243331)
              ·
                refine ⟨59504831772350067429364997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39669887848233378286243331 59504831772350067429364997)
                ·
                  refine ⟨11157155957315637643005937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59504831772350067429364997 11157155957315637643005937)
                  ·
                    refine ⟨8367866967986728232254453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11157155957315637643005937 8367866967986728232254453)
                    ·
                      refine ⟨784487528248755771773855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8367866967986728232254453 784487528248755771773855)
                      ·
                        rfl

theorem cell23_1527784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1527784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527784 prefixEnd_1527784 := by exact prefixLift 1527784
  have htrace : WordTrace (prefixWord ++ tailWord_1527784) baseStart_1527784 baseEnd_1527784 := by
    simpa [prefixWord, tailWord_1527784, baseEnd_1527784] using wordTrace_append hprefix tailTrace_1527784
  have hstable : (prefixWord ++ tailWord_1527784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527784).length < 2 ^ (prefixWord ++ tailWord_1527784).sum := by decide
  have hdescent : baseEnd_1527784 < baseStart_1527784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527789 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1527789 : Nat := 118140960795 + 1527789 * 2 ^ 59
def prefixEnd_1527789 : Nat := 4983230072969 + 3 ^ 40 * 1527789 * 2
def baseEnd_1527789 : Nat := 784490095652028252211333

theorem tailTrace_1527789 : CollatzResearch.WordTrace tailWord_1527789 prefixEnd_1527789 784490095652028252211333 := by
  unfold tailWord_1527789
  simp only [CollatzResearch.WordTrace]
  refine ⟨55723042662088853432962421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37148695108059235621974947 55723042662088853432962421)
  ·
    refine ⟨5224035249570830009340227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55723042662088853432962421 5224035249570830009340227)
    ·
      refine ⟨7836052874356245014010341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224035249570830009340227 7836052874356245014010341)
      ·
        refine ⟨1469259913941795940126939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7836052874356245014010341 1469259913941795940126939)
        ·
          refine ⟨2203889870912693910190409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469259913941795940126939 2203889870912693910190409)
          ·
            refine ⟨1652917403184520432642807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203889870912693910190409 1652917403184520432642807)
            ·
              refine ⟨2479376104776780648964211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652917403184520432642807 2479376104776780648964211)
              ·
                refine ⟨3719064157165170973446317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479376104776780648964211 3719064157165170973446317)
                ·
                  refine ⟨1394649058936939115042369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3719064157165170973446317 1394649058936939115042369)
                  ·
                    refine ⟨1045986794202704336281777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394649058936939115042369 1045986794202704336281777)
                    ·
                      refine ⟨784490095652028252211333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1045986794202704336281777 784490095652028252211333)
                      ·
                        rfl

theorem cell23_1527789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1527789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527789 prefixEnd_1527789 := by exact prefixLift 1527789
  have htrace : WordTrace (prefixWord ++ tailWord_1527789) baseStart_1527789 baseEnd_1527789 := by
    simpa [prefixWord, tailWord_1527789, baseEnd_1527789] using wordTrace_append hprefix tailTrace_1527789
  have hstable : (prefixWord ++ tailWord_1527789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527789).length < 2 ^ (prefixWord ++ tailWord_1527789).sum := by decide
  have hdescent : baseEnd_1527789 < baseStart_1527789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527804 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1527804 : Nat := 118140960795 + 1527804 * 2 ^ 59
def prefixEnd_1527804 : Nat := 4983230072969 + 3 ^ 40 * 1527804 * 2
def baseEnd_1527804 : Nat := 261499265953948564507921

theorem tailTrace_1527804 : CollatzResearch.WordTrace tailWord_1527804 prefixEnd_1527804 261499265953948564507921 := by
  unfold tailWord_1527804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27861794878517255497379233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37149059838023007329838977 27861794878517255497379233)
  ·
    refine ⟨20896346158887941623034425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27861794878517255497379233 20896346158887941623034425)
    ·
      refine ⟨15672259619165956217275819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20896346158887941623034425 15672259619165956217275819)
      ·
        refine ⟨23508389428748934325913729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15672259619165956217275819 23508389428748934325913729)
        ·
          refine ⟨17631292071561700744435297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23508389428748934325913729 17631292071561700744435297)
          ·
            refine ⟨13223469053671275558326473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17631292071561700744435297 13223469053671275558326473)
            ·
              refine ⟨9917601790253456668744855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13223469053671275558326473 9917601790253456668744855)
              ·
                refine ⟨14876402685380185003117283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9917601790253456668744855 14876402685380185003117283)
                ·
                  refine ⟨22314604028070277504675925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14876402685380185003117283 22314604028070277504675925)
                  ·
                    refine ⟨261499265953948564507921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22314604028070277504675925 261499265953948564507921)
                    ·
                      rfl

theorem cell23_1527804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1527804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527804 prefixEnd_1527804 := by exact prefixLift 1527804
  have htrace : WordTrace (prefixWord ++ tailWord_1527804) baseStart_1527804 baseEnd_1527804 := by
    simpa [prefixWord, tailWord_1527804, baseEnd_1527804] using wordTrace_append hprefix tailTrace_1527804
  have hstable : (prefixWord ++ tailWord_1527804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527804).length < 2 ^ (prefixWord ++ tailWord_1527804).sum := by decide
  have hdescent : baseEnd_1527804 < baseStart_1527804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527805 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_1527805 : Nat := 118140960795 + 1527805 * 2 ^ 59
def prefixEnd_1527805 : Nat := 4983230072969 + 3 ^ 40 * 1527805 * 2
def baseEnd_1527805 : Nat := 784498311342500189611259

theorem tailTrace_1527805 : CollatzResearch.WordTrace tailWord_1527805 prefixEnd_1527805 784498311342500189611259 := by
  unfold tailWord_1527805
  simp only [CollatzResearch.WordTrace]
  refine ⟨55723626230030888165544869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149084153353925443696579 55723626230030888165544869)
  ·
    refine ⟨10448179918130791531039663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55723626230030888165544869 10448179918130791531039663)
    ·
      refine ⟨15672269877196187296559495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448179918130791531039663 15672269877196187296559495)
      ·
        refine ⟨23508404815794280944839243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15672269877196187296559495 23508404815794280944839243)
        ·
          refine ⟨35262607223691421417258865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23508404815794280944839243 35262607223691421417258865)
          ·
            refine ⟨26446955417768566062944149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35262607223691421417258865 26446955417768566062944149)
            ·
              refine ⟨1239701035207901534200507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26446955417768566062944149 1239701035207901534200507)
              ·
                refine ⟨1859551552811852301300761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239701035207901534200507 1859551552811852301300761)
                ·
                  refine ⟨1394663664608889225975571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859551552811852301300761 1394663664608889225975571)
                  ·
                    refine ⟨2091995496913333838963357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394663664608889225975571 2091995496913333838963357)
                    ·
                      refine ⟨784498311342500189611259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2091995496913333838963357 784498311342500189611259)
                      ·
                        rfl

theorem cell23_1527805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_1527805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527805 prefixEnd_1527805 := by exact prefixLift 1527805
  have htrace : WordTrace (prefixWord ++ tailWord_1527805) baseStart_1527805 baseEnd_1527805 := by
    simpa [prefixWord, tailWord_1527805, baseEnd_1527805] using wordTrace_append hprefix tailTrace_1527805
  have hstable : (prefixWord ++ tailWord_1527805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527805).length < 2 ^ (prefixWord ++ tailWord_1527805).sum := by decide
  have hdescent : baseEnd_1527805 < baseStart_1527805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527811 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 4, 2]
def baseStart_1527811 : Nat := 118140960795 + 1527811 * 2 ^ 59
def prefixEnd_1527811 : Nat := 4983230072969 + 3 ^ 40 * 1527811 * 2
def baseEnd_1527811 : Nat := 784501392226427166136231

theorem tailTrace_1527811 : CollatzResearch.WordTrace tailWord_1527811 prefixEnd_1527811 784501392226427166136231 := by
  unfold tailWord_1527811
  simp only [CollatzResearch.WordTrace]
  refine ⟨55723845068009151190263287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149230045339434126842191 55723845068009151190263287)
  ·
    refine ⟨83585767602013726785394931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55723845068009151190263287 83585767602013726785394931)
    ·
      refine ⟨125378651403020590178092397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83585767602013726785394931 125378651403020590178092397)
      ·
        refine ⟨47016994276132721316784649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125378651403020590178092397 47016994276132721316784649)
        ·
          refine ⟨35262745707099540987588487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47016994276132721316784649 35262745707099540987588487)
          ·
            refine ⟨52894118560649311481382731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35262745707099540987588487 52894118560649311481382731)
            ·
              refine ⟨79341177840973967222074097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52894118560649311481382731 79341177840973967222074097)
              ·
                refine ⟨59505883380730475416555573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79341177840973967222074097 59505883380730475416555573)
                ·
                  refine ⟨5578676566943482070302085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59505883380730475416555573 5578676566943482070302085)
                  ·
                    refine ⟨1046001856301902888181641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578676566943482070302085 1046001856301902888181641)
                    ·
                      refine ⟨784501392226427166136231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046001856301902888181641 784501392226427166136231)
                      ·
                        rfl

theorem cell23_1527811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_1527811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527811 prefixEnd_1527811 := by exact prefixLift 1527811
  have htrace : WordTrace (prefixWord ++ tailWord_1527811) baseStart_1527811 baseEnd_1527811 := by
    simpa [prefixWord, tailWord_1527811, baseEnd_1527811] using wordTrace_append hprefix tailTrace_1527811
  have hstable : (prefixWord ++ tailWord_1527811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527811).length < 2 ^ (prefixWord ++ tailWord_1527811).sum := by decide
  have hdescent : baseEnd_1527811 < baseStart_1527811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527815 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1527815 : Nat := 118140960795 + 1527815 * 2 ^ 59
def prefixEnd_1527815 : Nat := 4983230072969 + 3 ^ 40 * 1527815 * 2
def baseEnd_1527815 : Nat := 784503446149045150486213

theorem tailTrace_1527815 : CollatzResearch.WordTrace tailWord_1527815 prefixEnd_1527815 784503446149045150486213 := by
  unfold tailWord_1527815
  simp only [CollatzResearch.WordTrace]
  refine ⟨55723990959994659873408899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149327306663106582272599 55723990959994659873408899)
  ·
    refine ⟨83585986439991989810113349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55723990959994659873408899 83585986439991989810113349)
    ·
      refine ⟨15672372457498498089396253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83585986439991989810113349 15672372457498498089396253)
      ·
        refine ⟨5877139671561936783523595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15672372457498498089396253 5877139671561936783523595)
        ·
          refine ⟨8815709507342905175285393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877139671561936783523595 8815709507342905175285393)
          ·
            refine ⟨6611782130507178881464045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8815709507342905175285393 6611782130507178881464045)
            ·
              refine ⟨2479418298940192080549017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6611782130507178881464045 2479418298940192080549017)
              ·
                refine ⟨1859563724205144060411763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479418298940192080549017 1859563724205144060411763)
                ·
                  refine ⟨2789345586307716090617645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859563724205144060411763 2789345586307716090617645)
                  ·
                    refine ⟨1046004594865393533981617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789345586307716090617645 1046004594865393533981617)
                    ·
                      refine ⟨784503446149045150486213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046004594865393533981617 784503446149045150486213)
                      ·
                        rfl

theorem cell23_1527815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1527815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527815 prefixEnd_1527815 := by exact prefixLift 1527815
  have htrace : WordTrace (prefixWord ++ tailWord_1527815) baseStart_1527815 baseEnd_1527815 := by
    simpa [prefixWord, tailWord_1527815, baseEnd_1527815] using wordTrace_append hprefix tailTrace_1527815
  have hstable : (prefixWord ++ tailWord_1527815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527815).length < 2 ^ (prefixWord ++ tailWord_1527815).sum := by decide
  have hdescent : baseEnd_1527815 < baseStart_1527815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527824 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_1527824 : Nat := 118140960795 + 1527824 * 2 ^ 59
def prefixEnd_1527824 : Nat := 4983230072969 + 3 ^ 40 * 1527824 * 2
def baseEnd_1527824 : Nat := 784508067474935615273671

theorem tailTrace_1527824 : CollatzResearch.WordTrace tailWord_1527824 prefixEnd_1527824 784508067474935615273671 := by
  unfold tailWord_1527824
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862159608481027205243263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37149546144641369606991017 27862159608481027205243263)
  ·
    refine ⟨41793239412721540807864895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27862159608481027205243263 41793239412721540807864895)
    ·
      refine ⟨62689859119082311211797343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41793239412721540807864895 62689859119082311211797343)
      ·
        refine ⟨94034788678623466817696015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62689859119082311211797343 94034788678623466817696015)
        ·
          refine ⟨141052183017935200226544023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94034788678623466817696015 141052183017935200226544023)
          ·
            refine ⟨211578274526902800339816035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141052183017935200226544023 211578274526902800339816035)
            ·
              refine ⟨317367411790354200509724053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211578274526902800339816035 317367411790354200509724053)
              ·
                refine ⟨14876597427672853148893315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317367411790354200509724053 14876597427672853148893315)
                ·
                  refine ⟨22314896141509279723339973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14876597427672853148893315 22314896141509279723339973)
                  ·
                    refine ⟨4184043026532989948126245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22314896141509279723339973 4184043026532989948126245)
                    ·
                      refine ⟨784508067474935615273671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4184043026532989948126245 784508067474935615273671)
                      ·
                        rfl

theorem cell23_1527824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_1527824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527824 prefixEnd_1527824 := by exact prefixLift 1527824
  have htrace : WordTrace (prefixWord ++ tailWord_1527824) baseStart_1527824 baseEnd_1527824 := by
    simpa [prefixWord, tailWord_1527824, baseEnd_1527824] using wordTrace_append hprefix tailTrace_1527824
  have hstable : (prefixWord ++ tailWord_1527824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527824).length < 2 ^ (prefixWord ++ tailWord_1527824).sum := by decide
  have hdescent : baseEnd_1527824 < baseStart_1527824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527845 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_1527845 : Nat := 118140960795 + 1527845 * 2 ^ 59
def prefixEnd_1527845 : Nat := 4983230072969 + 3 ^ 40 * 1527845 * 2
def baseEnd_1527845 : Nat := 784518850568680033111075

theorem tailTrace_1527845 : CollatzResearch.WordTrace tailWord_1527845 prefixEnd_1527845 784518850568680033111075 := by
  unfold tailWord_1527845
  simp only [CollatzResearch.WordTrace]
  refine ⟨55725085149885974997000989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37150056766590649998000659 55725085149885974997000989)
  ·
    refine ⟨20896906931207240623875371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55725085149885974997000989 20896906931207240623875371)
    ·
      refine ⟨31345360396810860935813057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20896906931207240623875371 31345360396810860935813057)
      ·
        refine ⟨23509020297608145701859793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31345360396810860935813057 23509020297608145701859793)
        ·
          refine ⟨17631765223206109276394845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23509020297608145701859793 17631765223206109276394845)
          ·
            refine ⟨6611911958702290978648067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17631765223206109276394845 6611911958702290978648067)
            ·
              refine ⟨9917867938053436467972101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611911958702290978648067 9917867938053436467972101)
              ·
                refine ⟨1859600238385019337744769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9917867938053436467972101 1859600238385019337744769)
                ·
                  refine ⟨1394700178788764503308577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859600238385019337744769 1394700178788764503308577)
                  ·
                    refine ⟨1046025134091573377481433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394700178788764503308577 1046025134091573377481433)
                    ·
                      refine ⟨784518850568680033111075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046025134091573377481433 784518850568680033111075)
                      ·
                        rfl

theorem cell23_1527845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_1527845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527845 prefixEnd_1527845 := by exact prefixLift 1527845
  have htrace : WordTrace (prefixWord ++ tailWord_1527845) baseStart_1527845 baseEnd_1527845 := by
    simpa [prefixWord, tailWord_1527845, baseEnd_1527845] using wordTrace_append hprefix tailTrace_1527845
  have hstable : (prefixWord ++ tailWord_1527845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527845).length < 2 ^ (prefixWord ++ tailWord_1527845).sum := by decide
  have hdescent : baseEnd_1527845 < baseStart_1527845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527861 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1527861 : Nat := 118140960795 + 1527861 * 2 ^ 59
def prefixEnd_1527861 : Nat := 4983230072969 + 3 ^ 40 * 1527861 * 2
def baseEnd_1527861 : Nat := 784527066259151970511001

theorem tailTrace_1527861 : CollatzResearch.WordTrace tailWord_1527861 prefixEnd_1527861 784527066259151970511001 := by
  unfold tailWord_1527861
  simp only [CollatzResearch.WordTrace]
  refine ⟨55725668717828009729583437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37150445811885339819722291 55725668717828009729583437)
  ·
    refine ⟨20897125769185503648593789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55725668717828009729583437 20897125769185503648593789)
    ·
      refine ⟨7836422163444563868222671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20897125769185503648593789 7836422163444563868222671)
      ·
        refine ⟨11754633245166845802334007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836422163444563868222671 11754633245166845802334007)
        ·
          refine ⟨17631949867750268703501011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754633245166845802334007 17631949867750268703501011)
          ·
            refine ⟨26447924801625403055251517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17631949867750268703501011 26447924801625403055251517)
            ·
              refine ⟨9917971800609526145719319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26447924801625403055251517 9917971800609526145719319)
              ·
                refine ⟨14876957700914289218578979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9917971800609526145719319 14876957700914289218578979)
                ·
                  refine ⟨22315436551371433827868469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14876957700914289218578979 22315436551371433827868469)
                  ·
                    refine ⟨2092072176691071921362669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22315436551371433827868469 2092072176691071921362669)
                    ·
                      refine ⟨784527066259151970511001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092072176691071921362669 784527066259151970511001)
                      ·
                        rfl

theorem cell23_1527861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1527861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527861 prefixEnd_1527861 := by exact prefixLift 1527861
  have htrace : WordTrace (prefixWord ++ tailWord_1527861) baseStart_1527861 baseEnd_1527861 := by
    simpa [prefixWord, tailWord_1527861, baseEnd_1527861] using wordTrace_append hprefix tailTrace_1527861
  have hstable : (prefixWord ++ tailWord_1527861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527861).length < 2 ^ (prefixWord ++ tailWord_1527861).sum := by decide
  have hdescent : baseEnd_1527861 < baseStart_1527861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527862 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1527862 : Nat := 118140960795 + 1527862 * 2 ^ 59
def prefixEnd_1527862 : Nat := 4983230072969 + 3 ^ 40 * 1527862 * 2
def baseEnd_1527862 : Nat := 784527579739806466598497

theorem tailTrace_1527862 : CollatzResearch.WordTrace tailWord_1527862 prefixEnd_1527862 784527579739806466598497 := by
  unfold tailWord_1527862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482856574426524181273115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37150470127216257933579893 3482856574426524181273115)
  ·
    refine ⟨5224284861639786271909673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482856574426524181273115 5224284861639786271909673)
    ·
      refine ⟨3918213646229839703932255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224284861639786271909673 3918213646229839703932255)
      ·
        refine ⟨5877320469344759555898383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918213646229839703932255 5877320469344759555898383)
        ·
          refine ⟨8815980704017139333847575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877320469344759555898383 8815980704017139333847575)
          ·
            refine ⟨13223971056025709000771363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815980704017139333847575 13223971056025709000771363)
            ·
              refine ⟨19835956584038563501157045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13223971056025709000771363 19835956584038563501157045)
              ·
                refine ⟨1859620929753615328233473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19835956584038563501157045 1859620929753615328233473)
                ·
                  refine ⟨1394715697315211496175105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859620929753615328233473 1394715697315211496175105)
                  ·
                    refine ⟨1046036772986408622131329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394715697315211496175105 1046036772986408622131329)
                    ·
                      refine ⟨784527579739806466598497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046036772986408622131329 784527579739806466598497)
                      ·
                        rfl

theorem cell23_1527862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1527862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527862 prefixEnd_1527862 := by exact prefixLift 1527862
  have htrace : WordTrace (prefixWord ++ tailWord_1527862) baseStart_1527862 baseEnd_1527862 := by
    simpa [prefixWord, tailWord_1527862, baseEnd_1527862] using wordTrace_append hprefix tailTrace_1527862
  have hstable : (prefixWord ++ tailWord_1527862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527862).length < 2 ^ (prefixWord ++ tailWord_1527862).sum := by decide
  have hdescent : baseEnd_1527862 < baseStart_1527862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527885 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1527885 : Nat := 118140960795 + 1527885 * 2 ^ 59
def prefixEnd_1527885 : Nat := 4983230072969 + 3 ^ 40 * 1527885 * 2
def baseEnd_1527885 : Nat := 87171043310539986290099

theorem tailTrace_1527885 : CollatzResearch.WordTrace tailWord_1527885 prefixEnd_1527885 87171043310539986290099 := by
  unfold tailWord_1527885
  simp only [CollatzResearch.WordTrace]
  refine ⟨55726544069741061828457109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37151029379827374552304739 55726544069741061828457109)
  ·
    refine ⟨2612181753269112273208927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55726544069741061828457109 2612181753269112273208927)
    ·
      refine ⟨3918272629903668409813391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612181753269112273208927 3918272629903668409813391)
      ·
        refine ⟨5877408944855502614720087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918272629903668409813391 5877408944855502614720087)
        ·
          refine ⟨8816113417283253922080131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877408944855502614720087 8816113417283253922080131)
          ·
            refine ⟨13224170125924880883120197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816113417283253922080131 13224170125924880883120197)
            ·
              refine ⟨2479531898610915165585037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13224170125924880883120197 2479531898610915165585037)
              ·
                refine ⟨929824461979093187094389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479531898610915165585037 929824461979093187094389)
                ·
                  refine ⟨87171043310539986290099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929824461979093187094389 87171043310539986290099)
                  ·
                    rfl

theorem cell23_1527885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1527885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527885 prefixEnd_1527885 := by exact prefixLift 1527885
  have htrace : WordTrace (prefixWord ++ tailWord_1527885) baseStart_1527885 baseEnd_1527885 := by
    simpa [prefixWord, tailWord_1527885, baseEnd_1527885] using wordTrace_append hprefix tailTrace_1527885
  have hstable : (prefixWord ++ tailWord_1527885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527885).length < 2 ^ (prefixWord ++ tailWord_1527885).sum := by decide
  have hdescent : baseEnd_1527885 < baseStart_1527885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527902 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1527902 : Nat := 118140960795 + 1527902 * 2 ^ 59
def prefixEnd_1527902 : Nat := 4983230072969 + 3 ^ 40 * 1527902 * 2
def baseEnd_1527902 : Nat := 87172013218442923344257

theorem tailTrace_1527902 : CollatzResearch.WordTrace tailWord_1527902 prefixEnd_1527902 87172013218442923344257 := by
  unfold tailWord_1527902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965895513834934216478245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37151442740452982487883973 6965895513834934216478245)
  ·
    refine ⟨1306105408844050165589671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6965895513834934216478245 1306105408844050165589671)
    ·
      refine ⟨1959158113266075248384507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306105408844050165589671 1959158113266075248384507)
      ·
        refine ⟨2938737169899112872576761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959158113266075248384507 2938737169899112872576761)
        ·
          refine ⟨2204052877424334654432571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938737169899112872576761 2204052877424334654432571)
          ·
            refine ⟨3306079316136501981648857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204052877424334654432571 3306079316136501981648857)
            ·
              refine ⟨2479559487102376486236643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306079316136501981648857 2479559487102376486236643)
              ·
                refine ⟨3719339230653564729354965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479559487102376486236643 3719339230653564729354965)
                ·
                  refine ⟨87172013218442923344257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3719339230653564729354965 87172013218442923344257)
                  ·
                    rfl

theorem cell23_1527902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1527902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527902 prefixEnd_1527902 := by exact prefixLift 1527902
  have htrace : WordTrace (prefixWord ++ tailWord_1527902) baseStart_1527902 baseEnd_1527902 := by
    simpa [prefixWord, tailWord_1527902, baseEnd_1527902] using wordTrace_append hprefix tailTrace_1527902
  have hstable : (prefixWord ++ tailWord_1527902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527902).length < 2 ^ (prefixWord ++ tailWord_1527902).sum := by decide
  have hdescent : baseEnd_1527902 < baseStart_1527902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527921 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1527921 : Nat := 118140960795 + 1527921 * 2 ^ 59
def prefixEnd_1527921 : Nat := 4983230072969 + 3 ^ 40 * 1527921 * 2
def baseEnd_1527921 : Nat := 784557875098421735760725

theorem tailTrace_1527921 : CollatzResearch.WordTrace tailWord_1527921 prefixEnd_1527921 784557875098421735760725 := by
  unfold tailWord_1527921
  simp only [CollatzResearch.WordTrace]
  refine ⟨55727857097610639976767617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37151904731740426651178411 55727857097610639976767617)
  ·
    refine ⟨41795892823207979982575713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55727857097610639976767617 41795892823207979982575713)
    ·
      refine ⟨31346919617405984986931785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41795892823207979982575713 31346919617405984986931785)
      ·
        refine ⟨23510189713054488740198839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31346919617405984986931785 23510189713054488740198839)
        ·
          refine ⟨35265284569581733110298259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23510189713054488740198839 35265284569581733110298259)
          ·
            refine ⟨52897926854372599665447389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35265284569581733110298259 52897926854372599665447389)
            ·
              refine ⟨19836722570389724874542771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52897926854372599665447389 19836722570389724874542771)
              ·
                refine ⟨29755083855584587311814157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19836722570389724874542771 29755083855584587311814157)
                ·
                  refine ⟨11158156445844220241930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29755083855584587311814157 11158156445844220241930309)
                  ·
                    refine ⟨2092154333595791295361933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11158156445844220241930309 2092154333595791295361933)
                    ·
                      refine ⟨784557875098421735760725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092154333595791295361933 784557875098421735760725)
                      ·
                        rfl

theorem cell23_1527921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1527921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527921 prefixEnd_1527921 := by exact prefixLift 1527921
  have htrace : WordTrace (prefixWord ++ tailWord_1527921) baseStart_1527921 baseEnd_1527921 := by
    simpa [prefixWord, tailWord_1527921, baseEnd_1527921] using wordTrace_append hprefix tailTrace_1527921
  have hstable : (prefixWord ++ tailWord_1527921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527921).length < 2 ^ (prefixWord ++ tailWord_1527921).sum := by decide
  have hdescent : baseEnd_1527921 < baseStart_1527921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527941 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 8]
def baseStart_1527941 : Nat := 118140960795 + 1527941 * 2 ^ 59
def prefixEnd_1527941 : Nat := 4983230072969 + 3 ^ 40 * 1527941 * 2
def baseEnd_1527941 : Nat := 87174238301279073056737

theorem tailTrace_1527941 : CollatzResearch.WordTrace tailWord_1527941 prefixEnd_1527941 87174238301279073056737 := by
  unfold tailWord_1527941
  simp only [CollatzResearch.WordTrace]
  refine ⟨55728586557538183392495677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37152391038358788928330451 55728586557538183392495677)
  ·
    refine ⟨20898219959076818772185879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55728586557538183392495677 20898219959076818772185879)
    ·
      refine ⟨31347329938615228158278819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20898219959076818772185879 31347329938615228158278819)
      ·
        refine ⟨47020994907922842237418229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31347329938615228158278819 47020994907922842237418229)
        ·
          refine ⟨4408218272617766459757959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47020994907922842237418229 4408218272617766459757959)
          ·
            refine ⟨6612327408926649689636939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408218272617766459757959 6612327408926649689636939)
            ·
              refine ⟨9918491113389974534455409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612327408926649689636939 9918491113389974534455409)
              ·
                refine ⟨7438868335042480900841557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9918491113389974534455409 7438868335042480900841557)
                ·
                  refine ⟨87174238301279073056737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7438868335042480900841557 87174238301279073056737)
                  ·
                    rfl

theorem cell23_1527941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_1527941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527941 prefixEnd_1527941 := by exact prefixLift 1527941
  have htrace : WordTrace (prefixWord ++ tailWord_1527941) baseStart_1527941 baseEnd_1527941 := by
    simpa [prefixWord, tailWord_1527941, baseEnd_1527941] using wordTrace_append hprefix tailTrace_1527941
  have hstable : (prefixWord ++ tailWord_1527941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527941).length < 2 ^ (prefixWord ++ tailWord_1527941).sum := by decide
  have hdescent : baseEnd_1527941 < baseStart_1527941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527962 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_1527962 : Nat := 118140960795 + 1527962 * 2 ^ 59
def prefixEnd_1527962 : Nat := 4983230072969 + 3 ^ 40 * 1527962 * 2
def baseEnd_1527962 : Nat := 261526309268418691782679

theorem tailTrace_1527962 : CollatzResearch.WordTrace tailWord_1527962 prefixEnd_1527962 261526309268418691782679 := by
  unfold tailWord_1527962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13932338122615525994752535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37152901660308069319340093 13932338122615525994752535)
  ·
    refine ⟨20898507183923288992128803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13932338122615525994752535 20898507183923288992128803)
    ·
      refine ⟨31347760775884933488193205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20898507183923288992128803 31347760775884933488193205)
      ·
        refine ⟨2938852572739212514518113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31347760775884933488193205 2938852572739212514518113)
        ·
          refine ⟨2204139429554409385888585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938852572739212514518113 2204139429554409385888585)
          ·
            refine ⟨1653104572165807039416439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204139429554409385888585 1653104572165807039416439)
            ·
              refine ⟨2479656858248710559124659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653104572165807039416439 2479656858248710559124659)
              ·
                refine ⟨3719485287373065838686989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479656858248710559124659 3719485287373065838686989)
                ·
                  refine ⟨1394806982764899689507621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3719485287373065838686989 1394806982764899689507621)
                  ·
                    refine ⟨261526309268418691782679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1394806982764899689507621 261526309268418691782679)
                    ·
                      rfl

theorem cell23_1527962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_1527962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527962 prefixEnd_1527962 := by exact prefixLift 1527962
  have htrace : WordTrace (prefixWord ++ tailWord_1527962) baseStart_1527962 baseEnd_1527962 := by
    simpa [prefixWord, tailWord_1527962, baseEnd_1527962] using wordTrace_append hprefix tailTrace_1527962
  have hstable : (prefixWord ++ tailWord_1527962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527962).length < 2 ^ (prefixWord ++ tailWord_1527962).sum := by decide
  have hdescent : baseEnd_1527962 < baseStart_1527962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527975 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 6]
def baseStart_1527975 : Nat := 118140960795 + 1527975 * 2 ^ 59
def prefixEnd_1527975 : Nat := 4983230072969 + 3 ^ 40 * 1527975 * 2
def baseEnd_1527975 : Nat := 87176178117084947165053

theorem tailTrace_1527975 : CollatzResearch.WordTrace tailWord_1527975 prefixEnd_1527975 87176178117084947165053 := by
  unfold tailWord_1527975
  simp only [CollatzResearch.WordTrace]
  refine ⟨55729826639415007199233379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37153217759610004799488919 55729826639415007199233379)
  ·
    refine ⟨83594739959122510798850069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55729826639415007199233379 83594739959122510798850069)
    ·
      refine ⟨3918503435583867693696097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83594739959122510798850069 3918503435583867693696097)
      ·
        refine ⟨2938877576687900770272073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3918503435583867693696097 2938877576687900770272073)
        ·
          refine ⟨2204158182515925577704055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938877576687900770272073 2204158182515925577704055)
          ·
            refine ⟨3306237273773888366556083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204158182515925577704055 3306237273773888366556083)
            ·
              refine ⟨4959355910660832549834125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306237273773888366556083 4959355910660832549834125)
              ·
                refine ⟨1859758466497812206187797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959355910660832549834125 1859758466497812206187797)
                ·
                  refine ⟨87176178117084947165053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1859758466497812206187797 87176178117084947165053)
                  ·
                    rfl

theorem cell23_1527975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 6].length) (baseStart_1527975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527975 prefixEnd_1527975 := by exact prefixLift 1527975
  have htrace : WordTrace (prefixWord ++ tailWord_1527975) baseStart_1527975 baseEnd_1527975 := by
    simpa [prefixWord, tailWord_1527975, baseEnd_1527975] using wordTrace_append hprefix tailTrace_1527975
  have hstable : (prefixWord ++ tailWord_1527975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527975).length < 2 ^ (prefixWord ++ tailWord_1527975).sum := by decide
  have hdescent : baseEnd_1527975 < baseStart_1527975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527995 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 2, 3, 2]
def baseStart_1527995 : Nat := 118140960795 + 1527995 * 2 ^ 59
def prefixEnd_1527995 : Nat := 4983230072969 + 3 ^ 40 * 1527995 * 2
def baseEnd_1527995 : Nat := 784595872666854446235385

theorem tailTrace_1527995 : CollatzResearch.WordTrace tailWord_1527995 prefixEnd_1527995 784595872666854446235385 := by
  unfold tailWord_1527995
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730556099342550614961439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37153704066228367076640959 55730556099342550614961439)
  ·
    refine ⟨83595834149013825922442159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55730556099342550614961439 83595834149013825922442159)
    ·
      refine ⟨125393751223520738883663239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83595834149013825922442159 125393751223520738883663239)
      ·
        refine ⟨188090626835281108325494859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125393751223520738883663239 188090626835281108325494859)
        ·
          refine ⟨282135940252921662488242289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188090626835281108325494859 282135940252921662488242289)
          ·
            refine ⟨211601955189691246866181717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282135940252921662488242289 211601955189691246866181717)
            ·
              refine ⟨2479710412379194299213067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 211601955189691246866181717 2479710412379194299213067)
              ·
                refine ⟨3719565618568791448819601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479710412379194299213067 3719565618568791448819601)
                ·
                  refine ⟨2789674213926593586614701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719565618568791448819601 2789674213926593586614701)
                  ·
                    refine ⟨1046127830222472594980513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789674213926593586614701 1046127830222472594980513)
                    ·
                      refine ⟨784595872666854446235385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046127830222472594980513 784595872666854446235385)
                      ·
                        rfl

theorem cell23_1527995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3, 2].length) (baseStart_1527995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1527995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1527995 prefixEnd_1527995 := by exact prefixLift 1527995
  have htrace : WordTrace (prefixWord ++ tailWord_1527995) baseStart_1527995 baseEnd_1527995 := by
    simpa [prefixWord, tailWord_1527995, baseEnd_1527995] using wordTrace_append hprefix tailTrace_1527995
  have hstable : (prefixWord ++ tailWord_1527995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527995).length < 2 ^ (prefixWord ++ tailWord_1527995).sum := by decide
  have hdescent : baseEnd_1527995 < baseStart_1527995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528042 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_1528042 : Nat := 118140960795 + 1528042 * 2 ^ 59
def prefixEnd_1528042 : Nat := 4983230072969 + 3 ^ 40 * 1528042 * 2
def baseEnd_1528042 : Nat := 784620006257615762347669

theorem tailTrace_1528042 : CollatzResearch.WordTrace tailWord_1528042 prefixEnd_1528042 784620006257615762347669 := by
  unfold tailWord_1528042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933067582543069410480595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37154846886781518427948253 13933067582543069410480595)
  ·
    refine ⟨20899601373814604115720893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13933067582543069410480595 20899601373814604115720893)
    ·
      refine ⟨7837350515180476543395335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20899601373814604115720893 7837350515180476543395335)
      ·
        refine ⟨11756025772770714815093003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7837350515180476543395335 11756025772770714815093003)
        ·
          refine ⟨17634038659156072222639505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11756025772770714815093003 17634038659156072222639505)
          ·
            refine ⟨13225528994367054166979629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17634038659156072222639505 13225528994367054166979629)
            ·
              refine ⟨4959573372887645312617361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13225528994367054166979629 4959573372887645312617361)
              ·
                refine ⟨3719680029665733984463021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959573372887645312617361 3719680029665733984463021)
                ·
                  refine ⟨1394880011124650244173633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3719680029665733984463021 1394880011124650244173633)
                  ·
                    refine ⟨1046160008343487683130225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394880011124650244173633 1046160008343487683130225)
                    ·
                      refine ⟨784620006257615762347669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046160008343487683130225 784620006257615762347669)
                      ·
                        rfl

theorem cell23_1528042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_1528042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528042 prefixEnd_1528042 := by exact prefixLift 1528042
  have htrace : WordTrace (prefixWord ++ tailWord_1528042) baseStart_1528042 baseEnd_1528042 := by
    simpa [prefixWord, tailWord_1528042, baseEnd_1528042] using wordTrace_append hprefix tailTrace_1528042
  have hstable : (prefixWord ++ tailWord_1528042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528042).length < 2 ^ (prefixWord ++ tailWord_1528042).sum := by decide
  have hdescent : baseEnd_1528042 < baseStart_1528042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528062 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1528062 : Nat := 118140960795 + 1528062 * 2 ^ 59
def prefixEnd_1528062 : Nat := 4983230072969 + 3 ^ 40 * 1528062 * 2
def baseEnd_1528062 : Nat := 784630275870705684097577

theorem tailTrace_1528062 : CollatzResearch.WordTrace tailWord_1528062 prefixEnd_1528062 784630275870705684097577 := by
  unfold tailWord_1528062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966624973762477632206305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37155333193399880705100293 6966624973762477632206305)
  ·
    refine ⟨5224968730321858224154729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6966624973762477632206305 5224968730321858224154729)
    ·
      refine ⟨3918726547741393668116047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224968730321858224154729 3918726547741393668116047)
      ·
        refine ⟨5878089821612090502174071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918726547741393668116047 5878089821612090502174071)
        ·
          refine ⟨8817134732418135753261107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878089821612090502174071 8817134732418135753261107)
          ·
            refine ⟨13225702098627203629891661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817134732418135753261107 13225702098627203629891661)
            ·
              refine ⟨4959638286985201361209373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13225702098627203629891661 4959638286985201361209373)
              ·
                refine ⟨1859864357619450510453515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959638286985201361209373 1859864357619450510453515)
                ·
                  refine ⟨2789796536429175765680273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859864357619450510453515 2789796536429175765680273)
                  ·
                    refine ⟨2092347402321881824260205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789796536429175765680273 2092347402321881824260205)
                    ·
                      refine ⟨784630275870705684097577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092347402321881824260205 784630275870705684097577)
                      ·
                        rfl

theorem cell23_1528062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1528062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528062 prefixEnd_1528062 := by exact prefixLift 1528062
  have htrace : WordTrace (prefixWord ++ tailWord_1528062) baseStart_1528062 baseEnd_1528062 := by
    simpa [prefixWord, tailWord_1528062, baseEnd_1528062] using wordTrace_append hprefix tailTrace_1528062
  have hstable : (prefixWord ++ tailWord_1528062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528062).length < 2 ^ (prefixWord ++ tailWord_1528062).sum := by decide
  have hdescent : baseEnd_1528062 < baseStart_1528062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528075 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 3]
def baseStart_1528075 : Nat := 118140960795 + 1528075 * 2 ^ 59
def prefixEnd_1528075 : Nat := 4983230072969 + 3 ^ 40 * 1528075 * 2
def baseEnd_1528075 : Nat := 784636951119214133235017

theorem tailTrace_1528075 : CollatzResearch.WordTrace tailWord_1528075 prefixEnd_1528075 784636951119214133235017 := by
  unfold tailWord_1528075
  simp only [CollatzResearch.WordTrace]
  refine ⟨55733473939052724277873679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37155649292701816185249119 55733473939052724277873679)
  ·
    refine ⟨83600210908579086416810519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55733473939052724277873679 83600210908579086416810519)
    ·
      refine ⟨125400316362868629625215779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83600210908579086416810519 125400316362868629625215779)
      ·
        refine ⟨188100474544302944437823669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125400316362868629625215779 188100474544302944437823669)
        ·
          refine ⟨17634419488528401041045969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188100474544302944437823669 17634419488528401041045969)
          ·
            refine ⟨13225814616396300780784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17634419488528401041045969 13225814616396300780784477)
            ·
              refine ⟨4959680481148612792794179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13225814616396300780784477 4959680481148612792794179)
              ·
                refine ⟨7439520721722919189191269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959680481148612792794179 7439520721722919189191269)
                ·
                  refine ⟨1394910135323047347973363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7439520721722919189191269 1394910135323047347973363)
                  ·
                    refine ⟨2092365202984571021960045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394910135323047347973363 2092365202984571021960045)
                    ·
                      refine ⟨784636951119214133235017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092365202984571021960045 784636951119214133235017)
                      ·
                        rfl

theorem cell23_1528075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 3].length) (baseStart_1528075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528075 prefixEnd_1528075 := by exact prefixLift 1528075
  have htrace : WordTrace (prefixWord ++ tailWord_1528075) baseStart_1528075 baseEnd_1528075 := by
    simpa [prefixWord, tailWord_1528075, baseEnd_1528075] using wordTrace_append hprefix tailTrace_1528075
  have hstable : (prefixWord ++ tailWord_1528075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528075).length < 2 ^ (prefixWord ++ tailWord_1528075).sum := by decide
  have hdescent : baseEnd_1528075 < baseStart_1528075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528085 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_1528085 : Nat := 118140960795 + 1528085 * 2 ^ 59
def prefixEnd_1528085 : Nat := 4983230072969 + 3 ^ 40 * 1528085 * 2
def baseEnd_1528085 : Nat := 784642085925759094109971

theorem tailTrace_1528085 : CollatzResearch.WordTrace tailWord_1528085 prefixEnd_1528085 784642085925759094109971 := by
  unfold tailWord_1528085
  simp only [CollatzResearch.WordTrace]
  refine ⟨55733838669016495985737709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37155892446010997323825139 55733838669016495985737709)
  ·
    refine ⟨20900189500881185994651641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55733838669016495985737709 20900189500881185994651641)
    ·
      refine ⟨15675142125660889495988731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20900189500881185994651641 15675142125660889495988731)
      ·
        refine ⟨23512713188491334243983097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15675142125660889495988731 23512713188491334243983097)
        ·
          refine ⟨17634534891368500682987323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23512713188491334243983097 17634534891368500682987323)
          ·
            refine ⟨26451802337052751024480985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17634534891368500682987323 26451802337052751024480985)
            ·
              refine ⟨19838851752789563268360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26451802337052751024480985 19838851752789563268360739)
              ·
                refine ⟨29758277629184344902541109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19838851752789563268360739 29758277629184344902541109)
                ·
                  refine ⟨2789838527736032334613229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29758277629184344902541109 2789838527736032334613229)
                  ·
                    refine ⟨1046189447901012125479961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789838527736032334613229 1046189447901012125479961)
                    ·
                      refine ⟨784642085925759094109971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046189447901012125479961 784642085925759094109971)
                      ·
                        rfl

theorem cell23_1528085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_1528085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528085 prefixEnd_1528085 := by exact prefixLift 1528085
  have htrace : WordTrace (prefixWord ++ tailWord_1528085) baseStart_1528085 baseEnd_1528085 := by
    simpa [prefixWord, tailWord_1528085, baseEnd_1528085] using wordTrace_append hprefix tailTrace_1528085
  have hstable : (prefixWord ++ tailWord_1528085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528085).length < 2 ^ (prefixWord ++ tailWord_1528085).sum := by decide
  have hdescent : baseEnd_1528085 < baseStart_1528085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528110 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1528110 : Nat := 118140960795 + 1528110 * 2 ^ 59
def prefixEnd_1528110 : Nat := 4983230072969 + 3 ^ 40 * 1528110 * 2
def baseEnd_1528110 : Nat := 784654922942121496297357

theorem tailTrace_1528110 : CollatzResearch.WordTrace tailWord_1528110 prefixEnd_1528110 784654922942121496297357 := by
  unfold tailWord_1528110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966843811740740656924723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37156500329283950170265189 6966843811740740656924723)
  ·
    refine ⟨10450265717611110985387085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6966843811740740656924723 10450265717611110985387085)
    ·
      refine ⟨3918849644104166619520157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10450265717611110985387085 3918849644104166619520157)
      ·
        refine ⟨1469568616539062482320059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3918849644104166619520157 1469568616539062482320059)
        ·
          refine ⟨2204352924808593723480089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469568616539062482320059 2204352924808593723480089)
          ·
            refine ⟨1653264693606445292610067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204352924808593723480089 1653264693606445292610067)
            ·
              refine ⟨2479897040409667938915101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653264693606445292610067 2479897040409667938915101)
              ·
                refine ⟨929961390153625477093163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479897040409667938915101 929961390153625477093163)
                ·
                  refine ⟨1394942085230438215639745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929961390153625477093163 1394942085230438215639745)
                  ·
                    refine ⟨1046206563922828661729809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394942085230438215639745 1046206563922828661729809)
                    ·
                      refine ⟨784654922942121496297357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046206563922828661729809 784654922942121496297357)
                      ·
                        rfl

theorem cell23_1528110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1528110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528110 prefixEnd_1528110 := by exact prefixLift 1528110
  have htrace : WordTrace (prefixWord ++ tailWord_1528110) baseStart_1528110 baseEnd_1528110 := by
    simpa [prefixWord, tailWord_1528110, baseEnd_1528110] using wordTrace_append hprefix tailTrace_1528110
  have hstable : (prefixWord ++ tailWord_1528110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528110).length < 2 ^ (prefixWord ++ tailWord_1528110).sum := by decide
  have hdescent : baseEnd_1528110 < baseStart_1528110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528115 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 4, 2]
def baseStart_1528115 : Nat := 118140960795 + 1528115 * 2 ^ 59
def prefixEnd_1528115 : Nat := 4983230072969 + 3 ^ 40 * 1528115 * 2
def baseEnd_1528115 : Nat := 784657490345393976734833

theorem tailTrace_1528115 : CollatzResearch.WordTrace tailWord_1528115 prefixEnd_1528115 784657490345393976734833 := by
  unfold tailWord_1528115
  simp only [CollatzResearch.WordTrace]
  refine ⟨55734932858907811109329799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37156621905938540739553199 55734932858907811109329799)
  ·
    refine ⟨83602399288361716663994699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55734932858907811109329799 83602399288361716663994699)
    ·
      refine ⟨125403598932542574995992049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83602399288361716663994699 125403598932542574995992049)
      ·
        refine ⟨94052699199406931246994037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125403598932542574995992049 94052699199406931246994037)
        ·
          refine ⟨8817440549944399804405691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94052699199406931246994037 8817440549944399804405691)
          ·
            refine ⟨13226160824916599706608537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817440549944399804405691 13226160824916599706608537)
            ·
              refine ⟨9919620618687449779956403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226160824916599706608537 9919620618687449779956403)
              ·
                refine ⟨14879430928031174669934605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9919620618687449779956403 14879430928031174669934605)
                ·
                  refine ⟨5579786598011690501225477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14879430928031174669934605 5579786598011690501225477)
                  ·
                    refine ⟨1046209987127191968979777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579786598011690501225477 1046209987127191968979777)
                    ·
                      refine ⟨784657490345393976734833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046209987127191968979777 784657490345393976734833)
                      ·
                        rfl

theorem cell23_1528115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4, 2].length) (baseStart_1528115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528115 prefixEnd_1528115 := by exact prefixLift 1528115
  have htrace : WordTrace (prefixWord ++ tailWord_1528115) baseStart_1528115 baseEnd_1528115 := by
    simpa [prefixWord, tailWord_1528115, baseEnd_1528115] using wordTrace_append hprefix tailTrace_1528115
  have hstable : (prefixWord ++ tailWord_1528115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528115).length < 2 ^ (prefixWord ++ tailWord_1528115).sum := by decide
  have hdescent : baseEnd_1528115 < baseStart_1528115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528128 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1528128 : Nat := 118140960795 + 1528128 * 2 ^ 59
def prefixEnd_1528128 : Nat := 4983230072969 + 3 ^ 40 * 1528128 * 2
def baseEnd_1528128 : Nat := 784664165593902425872273

theorem tailTrace_1528128 : CollatzResearch.WordTrace tailWord_1528128 prefixEnd_1528128 784664165593902425872273 := by
  unfold tailWord_1528128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867703503930357164776519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37156938005240476219702025 27867703503930357164776519)
  ·
    refine ⟨41801555255895535747164779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27867703503930357164776519 41801555255895535747164779)
    ·
      refine ⟨62702332883843303620747169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41801555255895535747164779 62702332883843303620747169)
      ·
        refine ⟨47026749662882477715560377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62702332883843303620747169 47026749662882477715560377)
        ·
          refine ⟨35270062247161858286670283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47026749662882477715560377 35270062247161858286670283)
          ·
            refine ⟨52905093370742787430005425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35270062247161858286670283 52905093370742787430005425)
            ·
              refine ⟨39678820028057090572504069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52905093370742787430005425 39678820028057090572504069)
              ·
                refine ⟨7439778755260704482344513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39678820028057090572504069 7439778755260704482344513)
                ·
                  refine ⟨5579834066445528361758385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439778755260704482344513 5579834066445528361758385)
                  ·
                    refine ⟨4184875549834146271318789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579834066445528361758385 4184875549834146271318789)
                    ·
                      refine ⟨784664165593902425872273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4184875549834146271318789 784664165593902425872273)
                      ·
                        rfl

theorem cell23_1528128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1528128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528128 prefixEnd_1528128 := by exact prefixLift 1528128
  have htrace : WordTrace (prefixWord ++ tailWord_1528128) baseStart_1528128 baseEnd_1528128 := by
    simpa [prefixWord, tailWord_1528128, baseEnd_1528128] using wordTrace_append hprefix tailTrace_1528128
  have hstable : (prefixWord ++ tailWord_1528128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528128).length < 2 ^ (prefixWord ++ tailWord_1528128).sum := by decide
  have hdescent : baseEnd_1528128 < baseStart_1528128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528189 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 5]
def baseStart_1528189 : Nat := 118140960795 + 1528189 * 2 ^ 59
def prefixEnd_1528189 : Nat := 4983230072969 + 3 ^ 40 * 1528189 * 2
def baseEnd_1528189 : Nat := 87188387545980743023277

theorem tailTrace_1528189 : CollatzResearch.WordTrace tailWord_1528189 prefixEnd_1528189 87188387545980743023277 := by
  unfold tailWord_1528189
  simp only [CollatzResearch.WordTrace]
  refine ⟨55737631860639721747523621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37158421240426481165015747 55737631860639721747523621)
  ·
    refine ⟨10450805973869947827660679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55737631860639721747523621 10450805973869947827660679)
    ·
      refine ⟨15676208960804921741491019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10450805973869947827660679 15676208960804921741491019)
      ·
        refine ⟨23514313441207382612236529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676208960804921741491019 23514313441207382612236529)
        ·
          refine ⟨17635735080905536959177397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23514313441207382612236529 17635735080905536959177397)
          ·
            refine ⟨1653350163834894089922881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17635735080905536959177397 1653350163834894089922881)
            ·
              refine ⟨1240012622876170567442161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653350163834894089922881 1240012622876170567442161)
              ·
                refine ⟨930009467157127925581621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240012622876170567442161 930009467157127925581621)
                ·
                  refine ⟨87188387545980743023277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930009467157127925581621 87188387545980743023277)
                  ·
                    rfl

theorem cell23_1528189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_1528189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528189 prefixEnd_1528189 := by exact prefixLift 1528189
  have htrace : WordTrace (prefixWord ++ tailWord_1528189) baseStart_1528189 baseEnd_1528189 := by
    simpa [prefixWord, tailWord_1528189, baseEnd_1528189] using wordTrace_append hprefix tailTrace_1528189
  have hstable : (prefixWord ++ tailWord_1528189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528189).length < 2 ^ (prefixWord ++ tailWord_1528189).sum := by decide
  have hdescent : baseEnd_1528189 < baseStart_1528189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528215 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 5, 4]
def baseStart_1528215 : Nat := 118140960795 + 1528215 * 2 ^ 59
def prefixEnd_1528215 : Nat := 4983230072969 + 3 ^ 40 * 1528215 * 2
def baseEnd_1528215 : Nat := 261569612803614528494791

theorem tailTrace_1528215 : CollatzResearch.WordTrace tailWord_1528215 prefixEnd_1528215 261569612803614528494791 := by
  unfold tailWord_1528215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55738580158545528187970099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37159053439030352125313399 55738580158545528187970099)
  ·
    refine ⟨83607870237818292281955149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55738580158545528187970099 83607870237818292281955149)
    ·
      refine ⟨31352951339181859605733181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83607870237818292281955149 31352951339181859605733181)
      ·
        refine ⟨11757356752193197352149943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31352951339181859605733181 11757356752193197352149943)
        ·
          refine ⟨17636035128289796028224915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757356752193197352149943 17636035128289796028224915)
          ·
            refine ⟨26454052692434694042337373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17636035128289796028224915 26454052692434694042337373)
            ·
              refine ⟨9920269759663010265876515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26454052692434694042337373 9920269759663010265876515)
              ·
                refine ⟨14880404639494515398814773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9920269759663010265876515 14880404639494515398814773)
                ·
                  refine ⟨1395037934952610818638885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14880404639494515398814773 1395037934952610818638885)
                  ·
                    refine ⟨261569612803614528494791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1395037934952610818638885 261569612803614528494791)
                    ·
                      rfl

theorem cell23_1528215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_1528215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528215 prefixEnd_1528215 := by exact prefixLift 1528215
  have htrace : WordTrace (prefixWord ++ tailWord_1528215) baseStart_1528215 baseEnd_1528215 := by
    simpa [prefixWord, tailWord_1528215, baseEnd_1528215] using wordTrace_append hprefix tailTrace_1528215
  have hstable : (prefixWord ++ tailWord_1528215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528215).length < 2 ^ (prefixWord ++ tailWord_1528215).sum := by decide
  have hdescent : baseEnd_1528215 < baseStart_1528215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528249 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 1, 4]
def baseStart_1528249 : Nat := 118140960795 + 1528249 * 2 ^ 59
def prefixEnd_1528249 : Nat := 4983230072969 + 3 ^ 40 * 1528249 * 2
def baseEnd_1528249 : Nat := 261575432251032150819739

theorem tailTrace_1528249 : CollatzResearch.WordTrace tailWord_1528249 prefixEnd_1528249 261575432251032150819739 := by
  unfold tailWord_1528249
  simp only [CollatzResearch.WordTrace]
  refine ⟨55739820240422351994707801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37159880160281567996471867 55739820240422351994707801)
  ·
    refine ⟨41804865180316763996030851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55739820240422351994707801 41804865180316763996030851)
    ·
      refine ⟨62707297770475145994046277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41804865180316763996030851 62707297770475145994046277)
      ·
        refine ⟨11757618331964089873883677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62707297770475145994046277 11757618331964089873883677)
        ·
          refine ⟨4409106874486533702706379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11757618331964089873883677 4409106874486533702706379)
          ·
            refine ⟨6613660311729800554059569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409106874486533702706379 6613660311729800554059569)
            ·
              refine ⟨4960245233797350415544677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613660311729800554059569 4960245233797350415544677)
              ·
                refine ⟨930045981337003202914627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4960245233797350415544677 930045981337003202914627)
                ·
                  refine ⟨1395068972005504804371941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930045981337003202914627 1395068972005504804371941)
                  ·
                    refine ⟨261575432251032150819739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1395068972005504804371941 261575432251032150819739)
                    ·
                      rfl

theorem cell23_1528249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_1528249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528249 prefixEnd_1528249 := by exact prefixLift 1528249
  have htrace : WordTrace (prefixWord ++ tailWord_1528249) baseStart_1528249 baseEnd_1528249 := by
    simpa [prefixWord, tailWord_1528249, baseEnd_1528249] using wordTrace_append hprefix tailTrace_1528249
  have hstable : (prefixWord ++ tailWord_1528249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528249).length < 2 ^ (prefixWord ++ tailWord_1528249).sum := by decide
  have hdescent : baseEnd_1528249 < baseStart_1528249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528282 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_1528282 : Nat := 118140960795 + 1528282 * 2 ^ 59
def prefixEnd_1528282 : Nat := 4983230072969 + 3 ^ 40 * 1528282 * 2
def baseEnd_1528282 : Nat := 784743241614694823346565

theorem tailTrace_1528282 : CollatzResearch.WordTrace tailWord_1528282 prefixEnd_1528282 784743241614694823346565 := by
  unfold tailWord_1528282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935255962325699657664775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37160682566201865753772733 13935255962325699657664775)
  ·
    refine ⟨20902883943488549486497163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935255962325699657664775 20902883943488549486497163)
    ·
      refine ⟨31354325915232824229745745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20902883943488549486497163 31354325915232824229745745)
      ·
        refine ⟨23515744436424618172309309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31354325915232824229745745 23515744436424618172309309)
        ·
          refine ⟨8818404163659231814615991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23515744436424618172309309 8818404163659231814615991)
          ·
            refine ⟨13227606245488847721923987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818404163659231814615991 13227606245488847721923987)
            ·
              refine ⟨19841409368233271582885981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13227606245488847721923987 19841409368233271582885981)
              ·
                refine ⟨7440528513087476843582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19841409368233271582885981 7440528513087476843582243)
                ·
                  refine ⟨11160792769631215265373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440528513087476843582243 11160792769631215265373365)
                  ·
                    refine ⟨1046324322152926431128753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11160792769631215265373365 1046324322152926431128753)
                    ·
                      refine ⟨784743241614694823346565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046324322152926431128753 784743241614694823346565)
                      ·
                        rfl

theorem cell23_1528282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_1528282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528282 prefixEnd_1528282 := by exact prefixLift 1528282
  have htrace : WordTrace (prefixWord ++ tailWord_1528282) baseStart_1528282 baseEnd_1528282 := by
    simpa [prefixWord, tailWord_1528282, baseEnd_1528282] using wordTrace_append hprefix tailTrace_1528282
  have hstable : (prefixWord ++ tailWord_1528282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528282).length < 2 ^ (prefixWord ++ tailWord_1528282).sum := by decide
  have hdescent : baseEnd_1528282 < baseStart_1528282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528325 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1528325 : Nat := 118140960795 + 1528325 * 2 ^ 59
def prefixEnd_1528325 : Nat := 4983230072969 + 3 ^ 40 * 1528325 * 2
def baseEnd_1528325 : Nat := 784765321282838155108867

theorem tailTrace_1528325 : CollatzResearch.WordTrace tailWord_1528325 prefixEnd_1528325 784765321282838155108867 := by
  unfold tailWord_1528325
  simp only [CollatzResearch.WordTrace]
  refine ⟨55742592188147016974474429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37161728125431344649649619 55742592188147016974474429)
  ·
    refine ⟨20903472070555131365427911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55742592188147016974474429 20903472070555131365427911)
    ·
      refine ⟨31355208105832697048141867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20903472070555131365427911 31355208105832697048141867)
      ·
        refine ⟨47032812158749045572212801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31355208105832697048141867 47032812158749045572212801)
        ·
          refine ⟨35274609119061784179159601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47032812158749045572212801 35274609119061784179159601)
          ·
            refine ⟨26455956839296338134369701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35274609119061784179159601 26455956839296338134369701)
            ·
              refine ⟨4960491907368063400194319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26455956839296338134369701 4960491907368063400194319)
              ·
                refine ⟨7440737861052095100291479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960491907368063400194319 7440737861052095100291479)
                ·
                  refine ⟨11161106791578142650437219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440737861052095100291479 11161106791578142650437219)
                  ·
                    refine ⟨16741660187367213975655829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11161106791578142650437219 16741660187367213975655829)
                    ·
                      refine ⟨784765321282838155108867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16741660187367213975655829 784765321282838155108867)
                      ·
                        rfl

theorem cell23_1528325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1528325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528325 prefixEnd_1528325 := by exact prefixLift 1528325
  have htrace : WordTrace (prefixWord ++ tailWord_1528325) baseStart_1528325 baseEnd_1528325 := by
    simpa [prefixWord, tailWord_1528325, baseEnd_1528325] using wordTrace_append hprefix tailTrace_1528325
  have hstable : (prefixWord ++ tailWord_1528325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528325).length < 2 ^ (prefixWord ++ tailWord_1528325).sum := by decide
  have hdescent : baseEnd_1528325 < baseStart_1528325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528333 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1528333 : Nat := 118140960795 + 1528333 * 2 ^ 59
def prefixEnd_1528333 : Nat := 4983230072969 + 3 ^ 40 * 1528333 * 2
def baseEnd_1528333 : Nat := 784769429128074123808831

theorem tailTrace_1528333 : CollatzResearch.WordTrace tailWord_1528333 prefixEnd_1528333 784769429128074123808831 := by
  unfold tailWord_1528333
  simp only [CollatzResearch.WordTrace]
  refine ⟨55742883972118034340765653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37161922648078689560510435 55742883972118034340765653)
  ·
    refine ⟨1306473843096516429861695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 55742883972118034340765653 1306473843096516429861695)
    ·
      refine ⟨1959710764644774644792543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306473843096516429861695 1959710764644774644792543)
      ·
        refine ⟨2939566146967161967188815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959710764644774644792543 2939566146967161967188815)
        ·
          refine ⟨4409349220450742950783223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939566146967161967188815 4409349220450742950783223)
          ·
            refine ⟨6614023830676114426174835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409349220450742950783223 6614023830676114426174835)
            ·
              refine ⟨9921035746014171639262253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614023830676114426174835 9921035746014171639262253)
              ·
                refine ⟨3720388404755314364723345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9921035746014171639262253 3720388404755314364723345)
                ·
                  refine ⟨2790291303566485773542509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720388404755314364723345 2790291303566485773542509)
                  ·
                    refine ⟨1046359238837432165078441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790291303566485773542509 1046359238837432165078441)
                    ·
                      refine ⟨784769429128074123808831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046359238837432165078441 784769429128074123808831)
                      ·
                        rfl

theorem cell23_1528333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1528333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528333 prefixEnd_1528333 := by exact prefixLift 1528333
  have htrace : WordTrace (prefixWord ++ tailWord_1528333) baseStart_1528333 baseEnd_1528333 := by
    simpa [prefixWord, tailWord_1528333, baseEnd_1528333] using wordTrace_append hprefix tailTrace_1528333
  have hstable : (prefixWord ++ tailWord_1528333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528333).length < 2 ^ (prefixWord ++ tailWord_1528333).sum := by decide
  have hdescent : baseEnd_1528333 < baseStart_1528333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528349 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1528349 : Nat := 118140960795 + 1528349 * 2 ^ 59
def prefixEnd_1528349 : Nat := 4983230072969 + 3 ^ 40 * 1528349 * 2
def baseEnd_1528349 : Nat := 784777644818546061208757

theorem tailTrace_1528349 : CollatzResearch.WordTrace tailWord_1528349 prefixEnd_1528349 784777644818546061208757 := by
  unfold tailWord_1528349
  simp only [CollatzResearch.WordTrace]
  refine ⟨55743467540060069073348101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37162311693373379382232067 55743467540060069073348101)
  ·
    refine ⟨10451900163761262951252769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55743467540060069073348101 10451900163761262951252769)
    ·
      refine ⟨7838925122820947213439577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10451900163761262951252769 7838925122820947213439577)
      ·
        refine ⟨5879193842115710410079683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7838925122820947213439577 5879193842115710410079683)
        ·
          refine ⟨8818790763173565615119525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879193842115710410079683 8818790763173565615119525)
          ·
            refine ⟨1653523268095043552834911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8818790763173565615119525 1653523268095043552834911)
            ·
              refine ⟨2480284902142565329252367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653523268095043552834911 2480284902142565329252367)
              ·
                refine ⟨3720427353213847993878551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480284902142565329252367 3720427353213847993878551)
                ·
                  refine ⟨5580641029820771990817827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720427353213847993878551 5580641029820771990817827)
                  ·
                    refine ⟨8370961544731157986226741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580641029820771990817827 8370961544731157986226741)
                    ·
                      refine ⟨784777644818546061208757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8370961544731157986226741 784777644818546061208757)
                      ·
                        rfl

theorem cell23_1528349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1528349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528349 prefixEnd_1528349 := by exact prefixLift 1528349
  have htrace : WordTrace (prefixWord ++ tailWord_1528349) baseStart_1528349 baseEnd_1528349 := by
    simpa [prefixWord, tailWord_1528349, baseEnd_1528349] using wordTrace_append hprefix tailTrace_1528349
  have hstable : (prefixWord ++ tailWord_1528349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528349).length < 2 ^ (prefixWord ++ tailWord_1528349).sum := by decide
  have hdescent : baseEnd_1528349 < baseStart_1528349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528352 : List Nat := [2, 1, 1, 6, 3, 10]
def baseStart_1528352 : Nat := 118140960795 + 1528352 * 2 ^ 59
def prefixEnd_1528352 : Nat := 4983230072969 + 3 ^ 40 * 1528352 * 2
def baseEnd_1528352 : Nat := 3229543972265471397001

theorem tailTrace_1528352 : CollatzResearch.WordTrace tailWord_1528352 prefixEnd_1528352 3229543972265471397001 := by
  unfold tailWord_1528352
  simp only [CollatzResearch.WordTrace]
  refine ⟨27871788479524600292853655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37162384639366133723804873 27871788479524600292853655)
  ·
    refine ⟨41807682719286900439280483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27871788479524600292853655 41807682719286900439280483)
    ·
      refine ⟨62711524078930350658920725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41807682719286900439280483 62711524078930350658920725)
      ·
        refine ⟨2939602691199860187136909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62711524078930350658920725 2939602691199860187136909)
        ·
          refine ⟨1102351009199947570176341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2939602691199860187136909 1102351009199947570176341)
          ·
            refine ⟨3229543972265471397001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1102351009199947570176341 3229543972265471397001)
            ·
              rfl

theorem cell23_1528352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 10].length) (baseStart_1528352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528352 prefixEnd_1528352 := by exact prefixLift 1528352
  have htrace : WordTrace (prefixWord ++ tailWord_1528352) baseStart_1528352 baseEnd_1528352 := by
    simpa [prefixWord, tailWord_1528352, baseEnd_1528352] using wordTrace_append hprefix tailTrace_1528352
  have hstable : (prefixWord ++ tailWord_1528352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528352).length < 2 ^ (prefixWord ++ tailWord_1528352).sum := by decide
  have hdescent : baseEnd_1528352 < baseStart_1528352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528389 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_1528389 : Nat := 118140960795 + 1528389 * 2 ^ 59
def prefixEnd_1528389 : Nat := 4983230072969 + 3 ^ 40 * 1528389 * 2
def baseEnd_1528389 : Nat := 784798184044725904708573

theorem tailTrace_1528389 : CollatzResearch.WordTrace tailWord_1528389 prefixEnd_1528389 784798184044725904708573 := by
  unfold tailWord_1528389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55744926459915155904804221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37163284306610103936536147 55744926459915155904804221)
  ·
    refine ⟨20904347422468183464301583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55744926459915155904804221 20904347422468183464301583)
    ·
      refine ⟨31356521133702275196452375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20904347422468183464301583 31356521133702275196452375)
      ·
        refine ⟨47034781700553412794678563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31356521133702275196452375 47034781700553412794678563)
        ·
          refine ⟨70552172550830119192017845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47034781700553412794678563 70552172550830119192017845)
          ·
            refine ⟨6614266176640323674251673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70552172550830119192017845 6614266176640323674251673)
            ·
              refine ⟨4960699632480242755688755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6614266176640323674251673 4960699632480242755688755)
              ·
                refine ⟨7441049448720364133533133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960699632480242755688755 7441049448720364133533133)
                ·
                  refine ⟨2790393543270136550074925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7441049448720364133533133 2790393543270136550074925)
                  ·
                    refine ⟨1046397578726301206278097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790393543270136550074925 1046397578726301206278097)
                    ·
                      refine ⟨784798184044725904708573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046397578726301206278097 784798184044725904708573)
                      ·
                        rfl

theorem cell23_1528389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_1528389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528389 prefixEnd_1528389 := by exact prefixLift 1528389
  have htrace : WordTrace (prefixWord ++ tailWord_1528389) baseStart_1528389 baseEnd_1528389 := by
    simpa [prefixWord, tailWord_1528389, baseEnd_1528389] using wordTrace_append hprefix tailTrace_1528389
  have hstable : (prefixWord ++ tailWord_1528389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528389).length < 2 ^ (prefixWord ++ tailWord_1528389).sum := by decide
  have hdescent : baseEnd_1528389 < baseStart_1528389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528509 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1528509 : Nat := 118140960795 + 1528509 * 2 ^ 59
def prefixEnd_1528509 : Nat := 4983230072969 + 3 ^ 40 * 1528509 * 2
def baseEnd_1528509 : Nat := 784859801723265435208021

theorem tailTrace_1528509 : CollatzResearch.WordTrace tailWord_1528509 prefixEnd_1528509 784859801723265435208021 := by
  unfold tailWord_1528509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55749303219480416399172581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37166202146320277599448387 55749303219480416399172581)
  ·
    refine ⟨10452994353652578074844859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55749303219480416399172581 10452994353652578074844859)
    ·
      refine ⟨15679491530478867112267289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10452994353652578074844859 15679491530478867112267289)
      ·
        refine ⟨11759618647859150334200467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15679491530478867112267289 11759618647859150334200467)
        ·
          refine ⟨17639427971788725501300701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11759618647859150334200467 17639427971788725501300701)
          ·
            refine ⟨6614785489420772062987763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17639427971788725501300701 6614785489420772062987763)
            ·
              refine ⟨9922178234131158094481645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614785489420772062987763 9922178234131158094481645)
              ·
                refine ⟨3720816837799184285430617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9922178234131158094481645 3720816837799184285430617)
                ·
                  refine ⟨2790612628349388214072963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720816837799184285430617 2790612628349388214072963)
                  ·
                    refine ⟨4185918942524082321109445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2790612628349388214072963 4185918942524082321109445)
                    ·
                      refine ⟨784859801723265435208021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4185918942524082321109445 784859801723265435208021)
                      ·
                        rfl

theorem cell23_1528509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1528509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528509 prefixEnd_1528509 := by exact prefixLift 1528509
  have htrace : WordTrace (prefixWord ++ tailWord_1528509) baseStart_1528509 baseEnd_1528509 := by
    simpa [prefixWord, tailWord_1528509, baseEnd_1528509] using wordTrace_append hprefix tailTrace_1528509
  have hstable : (prefixWord ++ tailWord_1528509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528509).length < 2 ^ (prefixWord ++ tailWord_1528509).sum := by decide
  have hdescent : baseEnd_1528509 < baseStart_1528509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528529 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_1528529 : Nat := 118140960795 + 1528529 * 2 ^ 59
def prefixEnd_1528529 : Nat := 4983230072969 + 3 ^ 40 * 1528529 * 2
def baseEnd_1528529 : Nat := 784870071336355356957929

theorem tailTrace_1528529 : CollatzResearch.WordTrace tailWord_1528529 prefixEnd_1528529 784870071336355356957929 := by
  unfold tailWord_1528529
  simp only [CollatzResearch.WordTrace]
  refine ⟨55750032679407959814900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37166688452938639876600427 55750032679407959814900641)
  ·
    refine ⟨41812524509555969861175481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55750032679407959814900641 41812524509555969861175481)
    ·
      refine ⟨31359393382166977395881611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41812524509555969861175481 31359393382166977395881611)
      ·
        refine ⟨47039090073250466093822417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31359393382166977395881611 47039090073250466093822417)
        ·
          refine ⟨35279317554937849570366813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47039090073250466093822417 35279317554937849570366813)
          ·
            refine ⟨13229744083101693588887555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35279317554937849570366813 13229744083101693588887555)
            ·
              refine ⟨19844616124652540383331333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229744083101693588887555 19844616124652540383331333)
              ·
                refine ⟨3720865523372351321874625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19844616124652540383331333 3720865523372351321874625)
                ·
                  refine ⟨2790649142529263491405969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720865523372351321874625 2790649142529263491405969)
                  ·
                    refine ⟨2092986856896947618554477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2790649142529263491405969 2092986856896947618554477)
                    ·
                      refine ⟨784870071336355356957929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2092986856896947618554477 784870071336355356957929)
                      ·
                        rfl

theorem cell23_1528529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_1528529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528529 prefixEnd_1528529 := by exact prefixLift 1528529
  have htrace : WordTrace (prefixWord ++ tailWord_1528529) baseStart_1528529 baseEnd_1528529 := by
    simpa [prefixWord, tailWord_1528529, baseEnd_1528529] using wordTrace_append hprefix tailTrace_1528529
  have hstable : (prefixWord ++ tailWord_1528529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528529).length < 2 ^ (prefixWord ++ tailWord_1528529).sum := by decide
  have hdescent : baseEnd_1528529 < baseStart_1528529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528549 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 6]
def baseStart_1528549 : Nat := 118140960795 + 1528549 * 2 ^ 59
def prefixEnd_1528549 : Nat := 4983230072969 + 3 ^ 40 * 1528549 * 2
def baseEnd_1528549 : Nat := 87208926772160586523093

theorem tailTrace_1528549 : CollatzResearch.WordTrace tailWord_1528549 prefixEnd_1528549 87208926772160586523093 := by
  unfold tailWord_1528549
  simp only [CollatzResearch.WordTrace]
  refine ⟨55750762139335503230628701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37167174759557002153752467 55750762139335503230628701)
  ·
    refine ⟨20906535802250813711485763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55750762139335503230628701 20906535802250813711485763)
    ·
      refine ⟨31359803703376220567228645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20906535802250813711485763 31359803703376220567228645)
      ·
        refine ⟨5879963194383041356355371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31359803703376220567228645 5879963194383041356355371)
        ·
          refine ⟨8819944791574562034533057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879963194383041356355371 8819944791574562034533057)
          ·
            refine ⟨6614958593680921525899793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8819944791574562034533057 6614958593680921525899793)
            ·
              refine ⟨4961218945260691144424845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6614958593680921525899793 4961218945260691144424845)
              ·
                refine ⟨1860457104472759179159317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4961218945260691144424845 1860457104472759179159317)
                ·
                  refine ⟨87208926772160586523093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1860457104472759179159317 87208926772160586523093)
                  ·
                    rfl

theorem cell23_1528549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_1528549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528549 prefixEnd_1528549 := by exact prefixLift 1528549
  have htrace : WordTrace (prefixWord ++ tailWord_1528549) baseStart_1528549 baseEnd_1528549 := by
    simpa [prefixWord, tailWord_1528549, baseEnd_1528549] using wordTrace_append hprefix tailTrace_1528549
  have hstable : (prefixWord ++ tailWord_1528549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528549).length < 2 ^ (prefixWord ++ tailWord_1528549).sum := by decide
  have hdescent : baseEnd_1528549 < baseStart_1528549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528586 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_1528586 : Nat := 118140960795 + 1528586 * 2 ^ 59
def prefixEnd_1528586 : Nat := 4983230072969 + 3 ^ 40 * 1528586 * 2
def baseEnd_1528586 : Nat := 784899339733661633945167

theorem tailTrace_1528586 : CollatzResearch.WordTrace tailWord_1528586 prefixEnd_1528586 784899339733661633945167 := by
  unfold tailWord_1528586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938027910050364637431403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37168074426800972366483741 13938027910050364637431403)
  ·
    refine ⟨20907041865075546956147105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938027910050364637431403 20907041865075546956147105)
    ·
      refine ⟨15680281398806660217110329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20907041865075546956147105 15680281398806660217110329)
      ·
        refine ⟨11760211049104995162832747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15680281398806660217110329 11760211049104995162832747)
        ·
          refine ⟨17640316573657492744249121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11760211049104995162832747 17640316573657492744249121)
          ·
            refine ⟨13230237430243119558186841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17640316573657492744249121 13230237430243119558186841)
            ·
              refine ⟨9922678072682339668640131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13230237430243119558186841 9922678072682339668640131)
              ·
                refine ⟨14884017109023509502960197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922678072682339668640131 14884017109023509502960197)
                ·
                  refine ⟨2790753207941908031805037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14884017109023509502960197 2790753207941908031805037)
                  ·
                    refine ⟨1046532452978215511926889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790753207941908031805037 1046532452978215511926889)
                    ·
                      refine ⟨784899339733661633945167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046532452978215511926889 784899339733661633945167)
                      ·
                        rfl

theorem cell23_1528586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_1528586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528586 prefixEnd_1528586 := by exact prefixLift 1528586
  have htrace : WordTrace (prefixWord ++ tailWord_1528586) baseStart_1528586 baseEnd_1528586 := by
    simpa [prefixWord, tailWord_1528586, baseEnd_1528586] using wordTrace_append hprefix tailTrace_1528586
  have hstable : (prefixWord ++ tailWord_1528586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528586).length < 2 ^ (prefixWord ++ tailWord_1528586).sum := by decide
  have hdescent : baseEnd_1528586 < baseStart_1528586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528593 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_1528593 : Nat := 118140960795 + 1528593 * 2 ^ 59
def prefixEnd_1528593 : Nat := 4983230072969 + 3 ^ 40 * 1528593 * 2
def baseEnd_1528593 : Nat := 784902934098243106557635

theorem tailTrace_1528593 : CollatzResearch.WordTrace tailWord_1528593 prefixEnd_1528593 784902934098243106557635 := by
  unfold tailWord_1528593
  simp only [CollatzResearch.WordTrace]
  refine ⟨55752366951176098745230433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37168244634117399163486955 55752366951176098745230433)
  ·
    refine ⟨41814275213382074058922825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55752366951176098745230433 41814275213382074058922825)
    ·
      refine ⟨31360706410036555544192119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41814275213382074058922825 31360706410036555544192119)
      ·
        refine ⟨47041059615054833316288179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31360706410036555544192119 47041059615054833316288179)
        ·
          refine ⟨70561589422582249974432269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47041059615054833316288179 70561589422582249974432269)
          ·
            refine ⟨26460596033468343740412101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70561589422582249974432269 26460596033468343740412101)
            ·
              refine ⟨4961361756275314451327269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26460596033468343740412101 4961361756275314451327269)
              ·
                refine ⟨930255329301621459623863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4961361756275314451327269 930255329301621459623863)
                ·
                  refine ⟨1395382993952432189435795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930255329301621459623863 1395382993952432189435795)
                  ·
                    refine ⟨2093074490928648284153693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395382993952432189435795 2093074490928648284153693)
                    ·
                      refine ⟨784902934098243106557635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093074490928648284153693 784902934098243106557635)
                      ·
                        rfl

theorem cell23_1528593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_1528593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528593 prefixEnd_1528593 := by exact prefixLift 1528593
  have htrace : WordTrace (prefixWord ++ tailWord_1528593) baseStart_1528593 baseEnd_1528593 := by
    simpa [prefixWord, tailWord_1528593, baseEnd_1528593] using wordTrace_append hprefix tailTrace_1528593
  have hstable : (prefixWord ++ tailWord_1528593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528593).length < 2 ^ (prefixWord ++ tailWord_1528593).sum := by decide
  have hdescent : baseEnd_1528593 < baseStart_1528593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528616 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1528616 : Nat := 118140960795 + 1528616 * 2 ^ 59
def prefixEnd_1528616 : Nat := 4983230072969 + 3 ^ 40 * 1528616 * 2
def baseEnd_1528616 : Nat := 784914744153296516570029

theorem tailTrace_1528616 : CollatzResearch.WordTrace tailWord_1528616 prefixEnd_1528616 784914744153296516570029 := by
  unfold tailWord_1528616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27876602915046386836658851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37168803886728515782211801 27876602915046386836658851)
  ·
    refine ⟨41814904372569580254988277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27876602915046386836658851 41814904372569580254988277)
    ·
      refine ⟨3920147284928398148905151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41814904372569580254988277 3920147284928398148905151)
      ·
        refine ⟨5880220927392597223357727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920147284928398148905151 5880220927392597223357727)
        ·
          refine ⟨8820331391088895835036591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5880220927392597223357727 8820331391088895835036591)
          ·
            refine ⟨13230497086633343752554887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820331391088895835036591 13230497086633343752554887)
            ·
              refine ⟨19845745629950015628832331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230497086633343752554887 19845745629950015628832331)
              ·
                refine ⟨29768618444925023443248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19845745629950015628832331 29768618444925023443248497)
                ·
                  refine ⟨22326463833693767582436373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29768618444925023443248497 22326463833693767582436373)
                  ·
                    refine ⟨1046552992204395355426705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22326463833693767582436373 1046552992204395355426705)
                    ·
                      refine ⟨784914744153296516570029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046552992204395355426705 784914744153296516570029)
                      ·
                        rfl

theorem cell23_1528616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1528616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528616 prefixEnd_1528616 := by exact prefixLift 1528616
  have htrace : WordTrace (prefixWord ++ tailWord_1528616) baseStart_1528616 baseEnd_1528616 := by
    simpa [prefixWord, tailWord_1528616, baseEnd_1528616] using wordTrace_append hprefix tailTrace_1528616
  have hstable : (prefixWord ++ tailWord_1528616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528616).length < 2 ^ (prefixWord ++ tailWord_1528616).sum := by decide
  have hdescent : baseEnd_1528616 < baseStart_1528616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528639 : List Nat := [1, 1, 2, 2, 5, 3, 9]
def baseStart_1528639 : Nat := 118140960795 + 1528639 * 2 ^ 59
def prefixEnd_1528639 : Nat := 4983230072969 + 3 ^ 40 * 1528639 * 2
def baseEnd_1528639 : Nat := 9690451286522838599783

theorem tailTrace_1528639 : CollatzResearch.WordTrace tailWord_1528639 prefixEnd_1528639 9690451286522838599783 := by
  unfold tailWord_1528639
  simp only [CollatzResearch.WordTrace]
  refine ⟨55754044709009448601404971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37169363139339632400936647 55754044709009448601404971)
  ·
    refine ⟨83631067063514172902107457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55754044709009448601404971 83631067063514172902107457)
    ·
      refine ⟨62723300297635629676580593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83631067063514172902107457 62723300297635629676580593)
      ·
        refine ⟨47042475223226722257435445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62723300297635629676580593 47042475223226722257435445)
        ·
          refine ⟨4410232052177505211634573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47042475223226722257435445 4410232052177505211634573)
          ·
            refine ⟨1653837019566564454362965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4410232052177505211634573 1653837019566564454362965)
            ·
              refine ⟨9690451286522838599783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1653837019566564454362965 9690451286522838599783)
              ·
                rfl

theorem cell23_1528639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 9].length) (baseStart_1528639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528639 prefixEnd_1528639 := by exact prefixLift 1528639
  have htrace : WordTrace (prefixWord ++ tailWord_1528639) baseStart_1528639 baseEnd_1528639 := by
    simpa [prefixWord, tailWord_1528639, baseEnd_1528639] using wordTrace_append hprefix tailTrace_1528639
  have hstable : (prefixWord ++ tailWord_1528639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528639).length < 2 ^ (prefixWord ++ tailWord_1528639).sum := by decide
  have hdescent : baseEnd_1528639 < baseStart_1528639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528644 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1528644 : Nat := 118140960795 + 1528644 * 2 ^ 59
def prefixEnd_1528644 : Nat := 4983230072969 + 3 ^ 40 * 1528644 * 2
def baseEnd_1528644 : Nat := 784929121611622407019901

theorem tailTrace_1528644 : CollatzResearch.WordTrace tailWord_1528644 prefixEnd_1528644 784929121611622407019901 := by
  unfold tailWord_1528644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27877113536995667227668493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37169484715994222970224657 27877113536995667227668493)
  ·
    refine ⟨10453917576373375210375685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27877113536995667227668493 10453917576373375210375685)
    ·
      refine ⟨1960109545570007851945441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10453917576373375210375685 1960109545570007851945441)
      ·
        refine ⟨1470082159177505888959081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960109545570007851945441 1470082159177505888959081)
        ·
          refine ⟨1102561619383129416719311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470082159177505888959081 1102561619383129416719311)
          ·
            refine ⟨1653842429074694125078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102561619383129416719311 1653842429074694125078967)
            ·
              refine ⟨2480763643612041187618451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653842429074694125078967 2480763643612041187618451)
              ·
                refine ⟨3721145465418061781427677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480763643612041187618451 3721145465418061781427677)
                ·
                  refine ⟨1395429549531773168035379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721145465418061781427677 1395429549531773168035379)
                  ·
                    refine ⟨2093144324297659752053069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395429549531773168035379 2093144324297659752053069)
                    ·
                      refine ⟨784929121611622407019901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093144324297659752053069 784929121611622407019901)
                      ·
                        rfl

theorem cell23_1528644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1528644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528644 prefixEnd_1528644 := by exact prefixLift 1528644
  have htrace : WordTrace (prefixWord ++ tailWord_1528644) baseStart_1528644 baseEnd_1528644 := by
    simpa [prefixWord, tailWord_1528644, baseEnd_1528644] using wordTrace_append hprefix tailTrace_1528644
  have hstable : (prefixWord ++ tailWord_1528644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528644).length < 2 ^ (prefixWord ++ tailWord_1528644).sum := by decide
  have hdescent : baseEnd_1528644 < baseStart_1528644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528897 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1528897 : Nat := 118140960795 + 1528897 * 2 ^ 59
def prefixEnd_1528897 : Nat := 4983230072969 + 3 ^ 40 * 1528897 * 2
def baseEnd_1528897 : Nat := 785059032217209917156237

theorem tailTrace_1528897 : CollatzResearch.WordTrace tailWord_1528897 prefixEnd_1528897 785059032217209917156237 := by
  unfold tailWord_1528897
  simp only [CollatzResearch.WordTrace]
  refine ⟨55763454742074758664296945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37175636494716505776197963 55763454742074758664296945)
  ·
    refine ⟨41822591056556068998222709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55763454742074758664296945 41822591056556068998222709)
    ·
      refine ⟨3920867911552131468583379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41822591056556068998222709 3920867911552131468583379)
      ·
        refine ⟨5881301867328197202875069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920867911552131468583379 5881301867328197202875069)
        ·
          refine ⟨2205488200248073951078151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5881301867328197202875069 2205488200248073951078151)
          ·
            refine ⟨3308232300372110926617227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205488200248073951078151 3308232300372110926617227)
            ·
              refine ⟨4962348450558166389925841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308232300372110926617227 4962348450558166389925841)
              ·
                refine ⟨3721761337918624792444381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962348450558166389925841 3721761337918624792444381)
                ·
                  refine ⟨1395660501719484297166643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721761337918624792444381 1395660501719484297166643)
                  ·
                    refine ⟨2093490752579226445749965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395660501719484297166643 2093490752579226445749965)
                    ·
                      refine ⟨785059032217209917156237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093490752579226445749965 785059032217209917156237)
                      ·
                        rfl

theorem cell23_1528897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1528897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528897 prefixEnd_1528897 := by exact prefixLift 1528897
  have htrace : WordTrace (prefixWord ++ tailWord_1528897) baseStart_1528897 baseEnd_1528897 := by
    simpa [prefixWord, tailWord_1528897, baseEnd_1528897] using wordTrace_append hprefix tailTrace_1528897
  have hstable : (prefixWord ++ tailWord_1528897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528897).length < 2 ^ (prefixWord ++ tailWord_1528897).sum := by decide
  have hdescent : baseEnd_1528897 < baseStart_1528897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528903 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1528903 : Nat := 118140960795 + 1528903 * 2 ^ 59
def prefixEnd_1528903 : Nat := 4983230072969 + 3 ^ 40 * 1528903 * 2
def baseEnd_1528903 : Nat := 785062113101136893681209

theorem tailTrace_1528903 : CollatzResearch.WordTrace tailWord_1528903 prefixEnd_1528903 785062113101136893681209 := by
  unfold tailWord_1528903
  simp only [CollatzResearch.WordTrace]
  refine ⟨55763673580053021689015363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37175782386702014459343575 55763673580053021689015363)
  ·
    refine ⟨83645510370079532533523045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55763673580053021689015363 83645510370079532533523045)
    ·
      refine ⟨15683533194389912350035571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83645510370079532533523045 15683533194389912350035571)
      ·
        refine ⟨23525299791584868525053357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15683533194389912350035571 23525299791584868525053357)
        ·
          refine ⟨8821987421844325696895009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23525299791584868525053357 8821987421844325696895009)
          ·
            refine ⟨6616490566383244272671257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8821987421844325696895009 6616490566383244272671257)
            ·
              refine ⟨4962367924787433204503443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6616490566383244272671257 4962367924787433204503443)
              ·
                refine ⟨7443551887181149806755165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962367924787433204503443 7443551887181149806755165)
                ·
                  refine ⟨2791331957692931177533187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7443551887181149806755165 2791331957692931177533187)
                  ·
                    refine ⟨4186997936539396766299781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2791331957692931177533187 4186997936539396766299781)
                    ·
                      refine ⟨785062113101136893681209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4186997936539396766299781 785062113101136893681209)
                      ·
                        rfl

theorem cell23_1528903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1528903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528903 prefixEnd_1528903 := by exact prefixLift 1528903
  have htrace : WordTrace (prefixWord ++ tailWord_1528903) baseStart_1528903 baseEnd_1528903 := by
    simpa [prefixWord, tailWord_1528903, baseEnd_1528903] using wordTrace_append hprefix tailTrace_1528903
  have hstable : (prefixWord ++ tailWord_1528903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528903).length < 2 ^ (prefixWord ++ tailWord_1528903).sum := by decide
  have hdescent : baseEnd_1528903 < baseStart_1528903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528914 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_1528914 : Nat := 118140960795 + 1528914 * 2 ^ 59
def prefixEnd_1528914 : Nat := 4983230072969 + 3 ^ 40 * 1528914 * 2
def baseEnd_1528914 : Nat := 785067761388336350643659

theorem tailTrace_1528914 : CollatzResearch.WordTrace tailWord_1528914 prefixEnd_1528914 785067761388336350643659 := by
  unfold tailWord_1528914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941018695753292641916449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37176049855342113711777197 13941018695753292641916449)
  ·
    refine ⟨10455764021814969481437337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13941018695753292641916449 10455764021814969481437337)
    ·
      refine ⟨7841823016361227111078003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10455764021814969481437337 7841823016361227111078003)
      ·
        refine ⟨11762734524541840666617005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841823016361227111078003 11762734524541840666617005)
        ·
          refine ⟨4411025446703190249981377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11762734524541840666617005 4411025446703190249981377)
          ·
            refine ⟨3308269085027392687486033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4411025446703190249981377 3308269085027392687486033)
            ·
              refine ⟨2481201813770544515614525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3308269085027392687486033 2481201813770544515614525)
              ·
                refine ⟨930450680163954193355447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2481201813770544515614525 930450680163954193355447)
                ·
                  refine ⟨1395676020245931290033171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930450680163954193355447 1395676020245931290033171)
                  ·
                    refine ⟨2093514030368896935049757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395676020245931290033171 2093514030368896935049757)
                    ·
                      refine ⟨785067761388336350643659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093514030368896935049757 785067761388336350643659)
                      ·
                        rfl

theorem cell23_1528914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_1528914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528914 prefixEnd_1528914 := by exact prefixLift 1528914
  have htrace : WordTrace (prefixWord ++ tailWord_1528914) baseStart_1528914 baseEnd_1528914 := by
    simpa [prefixWord, tailWord_1528914, baseEnd_1528914] using wordTrace_append hprefix tailTrace_1528914
  have hstable : (prefixWord ++ tailWord_1528914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528914).length < 2 ^ (prefixWord ++ tailWord_1528914).sum := by decide
  have hdescent : baseEnd_1528914 < baseStart_1528914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528920 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_1528920 : Nat := 118140960795 + 1528920 * 2 ^ 59
def prefixEnd_1528920 : Nat := 4983230072969 + 3 ^ 40 * 1528920 * 2
def baseEnd_1528920 : Nat := 785070842272263327168631

theorem tailTrace_1528920 : CollatzResearch.WordTrace tailWord_1528920 prefixEnd_1528920 785070842272263327168631 := by
  unfold tailWord_1528920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27882146810495716796192107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37176195747327622394922809 27882146810495716796192107)
  ·
    refine ⟨41823220215743575194288161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27882146810495716796192107 41823220215743575194288161)
    ·
      refine ⟨31367415161807681395716121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41823220215743575194288161 31367415161807681395716121)
      ·
        refine ⟨23525561371355761046787091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31367415161807681395716121 23525561371355761046787091)
        ·
          refine ⟨35288342057033641570180637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23525561371355761046787091 35288342057033641570180637)
          ·
            refine ⟨13233128271387615588817739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35288342057033641570180637 13233128271387615588817739)
            ·
              refine ⟨19849692407081423383226609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233128271387615588817739 19849692407081423383226609)
              ·
                refine ⟨14887269305311067537419957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19849692407081423383226609 14887269305311067537419957)
                ·
                  refine ⟨1395681497372912581633121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14887269305311067537419957 1395681497372912581633121)
                  ·
                    refine ⟨1046761123029684436224841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1395681497372912581633121 1046761123029684436224841)
                    ·
                      refine ⟨785070842272263327168631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046761123029684436224841 785070842272263327168631)
                      ·
                        rfl

theorem cell23_1528920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_1528920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528920 prefixEnd_1528920 := by exact prefixLift 1528920
  have htrace : WordTrace (prefixWord ++ tailWord_1528920) baseStart_1528920 baseEnd_1528920 := by
    simpa [prefixWord, tailWord_1528920, baseEnd_1528920] using wordTrace_append hprefix tailTrace_1528920
  have hstable : (prefixWord ++ tailWord_1528920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528920).length < 2 ^ (prefixWord ++ tailWord_1528920).sum := by decide
  have hdescent : baseEnd_1528920 < baseStart_1528920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528937 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 3, 2, 2]
def baseStart_1528937 : Nat := 118140960795 + 1528937 * 2 ^ 59
def prefixEnd_1528937 : Nat := 4983230072969 + 3 ^ 40 * 1528937 * 2
def baseEnd_1528937 : Nat := 785079571443389760656053

theorem tailTrace_1528937 : CollatzResearch.WordTrace tailWord_1528937 prefixEnd_1528937 785079571443389760656053 := by
  unfold tailWord_1528937
  simp only [CollatzResearch.WordTrace]
  refine ⟨55764913661929845495753065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37176609107953230330502043 55764913661929845495753065)
  ·
    refine ⟨41823685246447384121814799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55764913661929845495753065 41823685246447384121814799)
    ·
      refine ⟨62735527869671076182722199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41823685246447384121814799 62735527869671076182722199)
      ·
        refine ⟨94103291804506614274083299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62735527869671076182722199 94103291804506614274083299)
        ·
          refine ⟨141154937706759921411124949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94103291804506614274083299 141154937706759921411124949)
          ·
            refine ⟨3308318852502185658073241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141154937706759921411124949 3308318852502185658073241)
            ·
              refine ⟨2481239139376639243554931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3308318852502185658073241 2481239139376639243554931)
              ·
                refine ⟨3721858709064958865332397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481239139376639243554931 3721858709064958865332397)
                ·
                  refine ⟨1395697015899359574499649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721858709064958865332397 1395697015899359574499649)
                  ·
                    refine ⟨1046772761924519680874737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1395697015899359574499649 1046772761924519680874737)
                    ·
                      refine ⟨785079571443389760656053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1046772761924519680874737 785079571443389760656053)
                      ·
                        rfl

theorem cell23_1528937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2, 2].length) (baseStart_1528937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528937 prefixEnd_1528937 := by exact prefixLift 1528937
  have htrace : WordTrace (prefixWord ++ tailWord_1528937) baseStart_1528937 baseEnd_1528937 := by
    simpa [prefixWord, tailWord_1528937, baseEnd_1528937] using wordTrace_append hprefix tailTrace_1528937
  have hstable : (prefixWord ++ tailWord_1528937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528937).length < 2 ^ (prefixWord ++ tailWord_1528937).sum := by decide
  have hdescent : baseEnd_1528937 < baseStart_1528937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528970 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1528970 : Nat := 118140960795 + 1528970 * 2 ^ 59
def prefixEnd_1528970 : Nat := 4983230072969 + 3 ^ 40 * 1528970 * 2
def baseEnd_1528970 : Nat := 785096516304988131543401

theorem tailTrace_1528970 : CollatzResearch.WordTrace tailWord_1528970 prefixEnd_1528970 785096516304988131543401 := by
  unfold tailWord_1528970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941529317702573032926091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37177411513873528087802909 13941529317702573032926091)
  ·
    refine ⟨20912293976553859549389137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941529317702573032926091 20912293976553859549389137)
    ·
      refine ⟨15684220482415394662041853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20912293976553859549389137 15684220482415394662041853)
      ·
        refine ⟨5881582680905772998265695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15684220482415394662041853 5881582680905772998265695)
        ·
          refine ⟨8822374021358659497398543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881582680905772998265695 8822374021358659497398543)
          ·
            refine ⟨13233561032037989246097815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822374021358659497398543 13233561032037989246097815)
            ·
              refine ⟨19850341548056983869146723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233561032037989246097815 19850341548056983869146723)
              ·
                refine ⟨29775512322085475803720085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19850341548056983869146723 29775512322085475803720085)
                ·
                  refine ⟨1395727140097756678299379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29775512322085475803720085 1395727140097756678299379)
                  ·
                    refine ⟨2093590710146635017449069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395727140097756678299379 2093590710146635017449069)
                    ·
                      refine ⟨785096516304988131543401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093590710146635017449069 785096516304988131543401)
                      ·
                        rfl

theorem cell23_1528970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1528970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528970 prefixEnd_1528970 := by exact prefixLift 1528970
  have htrace : WordTrace (prefixWord ++ tailWord_1528970) baseStart_1528970 baseEnd_1528970 := by
    simpa [prefixWord, tailWord_1528970, baseEnd_1528970] using wordTrace_append hprefix tailTrace_1528970
  have hstable : (prefixWord ++ tailWord_1528970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528970).length < 2 ^ (prefixWord ++ tailWord_1528970).sum := by decide
  have hdescent : baseEnd_1528970 < baseStart_1528970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528993 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1528993 : Nat := 118140960795 + 1528993 * 2 ^ 59
def prefixEnd_1528993 : Nat := 4983230072969 + 3 ^ 40 * 1528993 * 2
def baseEnd_1528993 : Nat := 785108326360041541555795

theorem tailTrace_1528993 : CollatzResearch.WordTrace tailWord_1528993 prefixEnd_1528993 785108326360041541555795 := by
  unfold tailWord_1528993
  simp only [CollatzResearch.WordTrace]
  refine ⟨55766956149726967059791633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37177970766484644706527755 55766956149726967059791633)
  ·
    refine ⟨41825217112295225294843725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55766956149726967059791633 41825217112295225294843725)
    ·
      refine ⟨15684456417110709485566397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41825217112295225294843725 15684456417110709485566397)
      ·
        refine ⟨5881671156416516057087399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15684456417110709485566397 5881671156416516057087399)
        ·
          refine ⟨8822506734624774085631099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881671156416516057087399 8822506734624774085631099)
          ·
            refine ⟨13233760101937161128446649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822506734624774085631099 13233760101937161128446649)
            ·
              refine ⟨9925320076452870846334987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13233760101937161128446649 9925320076452870846334987)
              ·
                refine ⟨14887980114679306269502481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925320076452870846334987 14887980114679306269502481)
                ·
                  refine ⟨11165985086009479702126861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14887980114679306269502481 11165985086009479702126861)
                  ·
                    refine ⟨4187244407253554888297573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165985086009479702126861 4187244407253554888297573)
                    ·
                      refine ⟨785108326360041541555795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4187244407253554888297573 785108326360041541555795)
                      ·
                        rfl

theorem cell23_1528993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1528993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1528993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1528993 prefixEnd_1528993 := by exact prefixLift 1528993
  have htrace : WordTrace (prefixWord ++ tailWord_1528993) baseStart_1528993 baseEnd_1528993 := by
    simpa [prefixWord, tailWord_1528993, baseEnd_1528993] using wordTrace_append hprefix tailTrace_1528993
  have hstable : (prefixWord ++ tailWord_1528993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528993).length < 2 ^ (prefixWord ++ tailWord_1528993).sum := by decide
  have hdescent : baseEnd_1528993 < baseStart_1528993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3]
def baseStart_1529043 : Nat := 118140960795 + 1529043 * 2 ^ 59
def prefixEnd_1529043 : Nat := 4983230072969 + 3 ^ 40 * 1529043 * 2
def baseEnd_1529043 : Nat := 785134000392766345930565

theorem tailTrace_1529043 : CollatzResearch.WordTrace tailWord_1529043 prefixEnd_1529043 785134000392766345930565 := by
  unfold tailWord_1529043
  simp only [CollatzResearch.WordTrace]
  refine ⟨55768779799545825599111783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37179186533030550399407855 55768779799545825599111783)
  ·
    refine ⟨83653169699318738398667675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55768779799545825599111783 83653169699318738398667675)
    ·
      refine ⟨125479754548978107598001513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83653169699318738398667675 125479754548978107598001513)
      ·
        refine ⟨94109815911733580698501135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125479754548978107598001513 94109815911733580698501135)
        ·
          refine ⟨141164723867600371047751703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94109815911733580698501135 141164723867600371047751703)
          ·
            refine ⟨211747085801400556571627555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141164723867600371047751703 211747085801400556571627555)
            ·
              refine ⟨317620628702100834857441333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211747085801400556571627555 317620628702100834857441333)
              ·
                refine ⟨29776933940821953267885125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317620628702100834857441333 29776933940821953267885125)
                ·
                  refine ⟨5583175113904116237728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29776933940821953267885125 5583175113904116237728461)
                  ·
                    refine ⟨2093690667714043589148173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5583175113904116237728461 2093690667714043589148173)
                    ·
                      refine ⟨785134000392766345930565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093690667714043589148173 785134000392766345930565)
                      ·
                        rfl

theorem cell23_1529043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_1529043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529043 prefixEnd_1529043 := by exact prefixLift 1529043
  have htrace : WordTrace (prefixWord ++ tailWord_1529043) baseStart_1529043 baseEnd_1529043 := by
    simpa [prefixWord, tailWord_1529043, baseEnd_1529043] using wordTrace_append hprefix tailTrace_1529043
  have hstable : (prefixWord ++ tailWord_1529043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529043).length < 2 ^ (prefixWord ++ tailWord_1529043).sum := by decide
  have hdescent : baseEnd_1529043 < baseStart_1529043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529140 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1529140 : Nat := 118140960795 + 1529140 * 2 ^ 59
def prefixEnd_1529140 : Nat := 4983230072969 + 3 ^ 40 * 1529140 * 2
def baseEnd_1529140 : Nat := 87242645335139162935291

theorem tailTrace_1529140 : CollatzResearch.WordTrace tailWord_1529140 prefixEnd_1529140 87242645335139162935291 := by
  unfold tailWord_1529140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27886158840097205582696437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37181545120129607443595249 27886158840097205582696437)
  ·
    refine ⟨2614327391259113023377791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27886158840097205582696437 2614327391259113023377791)
    ·
      refine ⟨3921491086888669535066687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614327391259113023377791 3921491086888669535066687)
      ·
        refine ⟨5882236630333004302600031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921491086888669535066687 5882236630333004302600031)
        ·
          refine ⟨8823354945499506453900047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882236630333004302600031 8823354945499506453900047)
          ·
            refine ⟨13235032418249259680850071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8823354945499506453900047 13235032418249259680850071)
            ·
              refine ⟨19852548627373889521275107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13235032418249259680850071 19852548627373889521275107)
              ·
                refine ⟨29778822941060834281912661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19852548627373889521275107 29778822941060834281912661)
                ·
                  refine ⟨87242645335139162935291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29778822941060834281912661 87242645335139162935291)
                  ·
                    rfl

theorem cell23_1529140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1529140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529140 prefixEnd_1529140 := by exact prefixLift 1529140
  have htrace : WordTrace (prefixWord ++ tailWord_1529140) baseStart_1529140 baseEnd_1529140 := by
    simpa [prefixWord, tailWord_1529140, baseEnd_1529140] using wordTrace_append hprefix tailTrace_1529140
  have hstable : (prefixWord ++ tailWord_1529140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529140).length < 2 ^ (prefixWord ++ tailWord_1529140).sum := by decide
  have hdescent : baseEnd_1529140 < baseStart_1529140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529170 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1529170 : Nat := 118140960795 + 1529170 * 2 ^ 59
def prefixEnd_1529170 : Nat := 4983230072969 + 3 ^ 40 * 1529170 * 2
def baseEnd_1529170 : Nat := 261733070811962449680827

theorem tailTrace_1529170 : CollatzResearch.WordTrace tailWord_1529170 prefixEnd_1529170 261733070811962449680827 := by
  unfold tailWord_1529170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943352967521431572246241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37182274580057150859323309 13943352967521431572246241)
  ·
    refine ⟨10457514725641073679184681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13943352967521431572246241 10457514725641073679184681)
    ·
      refine ⟨7843136044230805259388511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10457514725641073679184681 7843136044230805259388511)
      ·
        refine ⟨11764704066346207889082767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843136044230805259388511 11764704066346207889082767)
        ·
          refine ⟨17647056099519311833624151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11764704066346207889082767 17647056099519311833624151)
          ·
            refine ⟨26470584149278967750436227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17647056099519311833624151 26470584149278967750436227)
            ·
              refine ⟨39705876223918451625654341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26470584149278967750436227 39705876223918451625654341)
              ·
                refine ⟨7444851791984709679810189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39705876223918451625654341 7444851791984709679810189)
                ·
                  refine ⟨2791819421994266129928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7444851791984709679810189 2791819421994266129928821)
                  ·
                    refine ⟨261733070811962449680827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2791819421994266129928821 261733070811962449680827)
                    ·
                      rfl

theorem cell23_1529170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1529170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529170 prefixEnd_1529170 := by exact prefixLift 1529170
  have htrace : WordTrace (prefixWord ++ tailWord_1529170) baseStart_1529170 baseEnd_1529170 := by
    simpa [prefixWord, tailWord_1529170, baseEnd_1529170] using wordTrace_append hprefix tailTrace_1529170
  have hstable : (prefixWord ++ tailWord_1529170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529170).length < 2 ^ (prefixWord ++ tailWord_1529170).sum := by decide
  have hdescent : baseEnd_1529170 < baseStart_1529170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529187 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 1, 5]
def baseStart_1529187 : Nat := 118140960795 + 1529187 * 2 ^ 59
def prefixEnd_1529187 : Nat := 4983230072969 + 3 ^ 40 * 1529187 * 2
def baseEnd_1529187 : Nat := 261735980535671260843301

theorem tailTrace_1529187 : CollatzResearch.WordTrace tailWord_1529187 prefixEnd_1529187 261735980535671260843301 := by
  unfold tailWord_1529187
  simp only [CollatzResearch.WordTrace]
  refine ⟨55774031911024138192353815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37182687940682758794902543 55774031911024138192353815)
  ·
    refine ⟨83661047866536207288530723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55774031911024138192353815 83661047866536207288530723)
    ·
      refine ⟨125491571799804310932796085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83661047866536207288530723 125491571799804310932796085)
      ·
        refine ⟨11764834856231654149949633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125491571799804310932796085 11764834856231654149949633)
        ·
          refine ⟨8823626142173740612462225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11764834856231654149949633 8823626142173740612462225)
          ·
            refine ⟨6617719606630305459346669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8823626142173740612462225 6617719606630305459346669)
            ·
              refine ⟨2481644852486364547255001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6617719606630305459346669 2481644852486364547255001)
              ·
                refine ⟨1861233639364773410441251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481644852486364547255001 1861233639364773410441251)
                ·
                  refine ⟨2791850459047160115661877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861233639364773410441251 2791850459047160115661877)
                  ·
                    refine ⟨261735980535671260843301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2791850459047160115661877 261735980535671260843301)
                    ·
                      rfl

theorem cell23_1529187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 5].length) (baseStart_1529187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529187 prefixEnd_1529187 := by exact prefixLift 1529187
  have htrace : WordTrace (prefixWord ++ tailWord_1529187) baseStart_1529187 baseEnd_1529187 := by
    simpa [prefixWord, tailWord_1529187, baseEnd_1529187] using wordTrace_append hprefix tailTrace_1529187
  have hstable : (prefixWord ++ tailWord_1529187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529187).length < 2 ^ (prefixWord ++ tailWord_1529187).sum := by decide
  have hdescent : baseEnd_1529187 < baseStart_1529187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529200 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_1529200 : Nat := 118140960795 + 1529200 * 2 ^ 59
def prefixEnd_1529200 : Nat := 4983230072969 + 3 ^ 40 * 1529200 * 2
def baseEnd_1529200 : Nat := 261738205618507410555781

theorem tailTrace_1529200 : CollatzResearch.WordTrace tailWord_1529200 prefixEnd_1529200 261738205618507410555781 := by
  unfold tailWord_1529200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887253029988520706288527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37183004039984694275051369 27887253029988520706288527)
  ·
    refine ⟨41830879544982781059432791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27887253029988520706288527 41830879544982781059432791)
    ·
      refine ⟨62746319317474171589149187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41830879544982781059432791 62746319317474171589149187)
      ·
        refine ⟨94119478976211257383723781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62746319317474171589149187 94119478976211257383723781)
        ·
          refine ⟨17647402308039610759448209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94119478976211257383723781 17647402308039610759448209)
          ·
            refine ⟨13235551731029708069586157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17647402308039610759448209 13235551731029708069586157)
            ·
              refine ⟨4963331899136140526094809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13235551731029708069586157 4963331899136140526094809)
              ·
                refine ⟨3722498924352105394571107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963331899136140526094809 3722498924352105394571107)
                ·
                  refine ⟨5583748386528158091856661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3722498924352105394571107 5583748386528158091856661)
                  ·
                    refine ⟨261738205618507410555781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5583748386528158091856661 261738205618507410555781)
                    ·
                      rfl

theorem cell23_1529200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_1529200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529200 prefixEnd_1529200 := by exact prefixLift 1529200
  have htrace : WordTrace (prefixWord ++ tailWord_1529200) baseStart_1529200 baseEnd_1529200 := by
    simpa [prefixWord, tailWord_1529200, baseEnd_1529200] using wordTrace_append hprefix tailTrace_1529200
  have hstable : (prefixWord ++ tailWord_1529200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529200).length < 2 ^ (prefixWord ++ tailWord_1529200).sum := by decide
  have hdescent : baseEnd_1529200 < baseStart_1529200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529247 : List Nat := [1, 1, 2, 5, 1, 3, 3, 7]
def baseStart_1529247 : Nat := 118140960795 + 1529247 * 2 ^ 59
def prefixEnd_1529247 : Nat := 4983230072969 + 3 ^ 40 * 1529247 * 2
def baseEnd_1529247 : Nat := 29082916683195686954801

theorem tailTrace_1529247 : CollatzResearch.WordTrace tailWord_1529247 prefixEnd_1529247 29082916683195686954801 := by
  unfold tailWord_1529247
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776220290806768439537995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37184146860537845626358663 55776220290806768439537995)
  ·
    refine ⟨83664330436210152659306993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55776220290806768439537995 83664330436210152659306993)
    ·
      refine ⟨62748247827157614494480245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83664330436210152659306993 62748247827157614494480245)
      ·
        refine ⟨5882648233796026358857523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62748247827157614494480245 5882648233796026358857523)
        ·
          refine ⟨8823972350694039538286285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882648233796026358857523 8823972350694039538286285)
          ·
            refine ⟨3308989631510264826857357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8823972350694039538286285 3308989631510264826857357)
            ·
              refine ⟨1240871111816349310071509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3308989631510264826857357 1240871111816349310071509)
              ·
                refine ⟨29082916683195686954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1240871111816349310071509 29082916683195686954801)
                ·
                  rfl

theorem cell23_1529247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 7].length) (baseStart_1529247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529247 prefixEnd_1529247 := by exact prefixLift 1529247
  have htrace : WordTrace (prefixWord ++ tailWord_1529247) baseStart_1529247 baseEnd_1529247 := by
    simpa [prefixWord, tailWord_1529247, baseEnd_1529247] using wordTrace_append hprefix tailTrace_1529247
  have hstable : (prefixWord ++ tailWord_1529247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529247).length < 2 ^ (prefixWord ++ tailWord_1529247).sum := by decide
  have hdescent : baseEnd_1529247 < baseStart_1529247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529261 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1529261 : Nat := 118140960795 + 1529261 * 2 ^ 59
def prefixEnd_1529261 : Nat := 4983230072969 + 3 ^ 40 * 1529261 * 2
def baseEnd_1529261 : Nat := 785245939175446493004563

theorem tailTrace_1529261 : CollatzResearch.WordTrace tailWord_1529261 prefixEnd_1529261 785245939175446493004563 := by
  unfold tailWord_1529261
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776730912756048830547637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37184487275170699220365091 55776730912756048830547637)
  ·
    refine ⟨5229068523070879577863841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55776730912756048830547637 5229068523070879577863841)
    ·
      refine ⟨3921801392303159683397881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5229068523070879577863841 3921801392303159683397881)
      ·
        refine ⟨2941351044227369762548411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3921801392303159683397881 2941351044227369762548411)
        ·
          refine ⟨4412026566341054643822617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941351044227369762548411 4412026566341054643822617)
          ·
            refine ⟨3309019924755790982866963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412026566341054643822617 3309019924755790982866963)
            ·
              refine ⟨4963529887133686474300445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309019924755790982866963 4963529887133686474300445)
              ·
                refine ⟨1861323707675132427862667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4963529887133686474300445 1861323707675132427862667)
                ·
                  refine ⟨2791985561512698641794001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861323707675132427862667 2791985561512698641794001)
                  ·
                    refine ⟨2093989171134523981345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2791985561512698641794001 2093989171134523981345501)
                    ·
                      refine ⟨785245939175446493004563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2093989171134523981345501 785245939175446493004563)
                      ·
                        rfl

theorem cell23_1529261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1529261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529261 prefixEnd_1529261 := by exact prefixLift 1529261
  have htrace : WordTrace (prefixWord ++ tailWord_1529261) baseStart_1529261 baseEnd_1529261 := by
    simpa [prefixWord, tailWord_1529261, baseEnd_1529261] using wordTrace_append hprefix tailTrace_1529261
  have hstable : (prefixWord ++ tailWord_1529261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529261).length < 2 ^ (prefixWord ++ tailWord_1529261).sum := by decide
  have hdescent : baseEnd_1529261 < baseStart_1529261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529280 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1529280 : Nat := 118140960795 + 1529280 * 2 ^ 59
def prefixEnd_1529280 : Nat := 4983230072969 + 3 ^ 40 * 1529280 * 2
def baseEnd_1529280 : Nat := 785255695307881918666975

theorem tailTrace_1529280 : CollatzResearch.WordTrace tailWord_1529280 prefixEnd_1529280 785255695307881918666975 := by
  unfold tailWord_1529280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888711949843607537744647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37184949266458143383659529 27888711949843607537744647)
  ·
    refine ⟨41833067924765411306616971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27888711949843607537744647 41833067924765411306616971)
    ·
      refine ⟨62749601887148116959925457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41833067924765411306616971 62749601887148116959925457)
      ·
        refine ⟨47062201415361087719944093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62749601887148116959925457 47062201415361087719944093)
        ·
          refine ⟨17648325530760407894979035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47062201415361087719944093 17648325530760407894979035)
          ·
            refine ⟨26472488296140611842468553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648325530760407894979035 26472488296140611842468553)
            ·
              refine ⟨19854366222105458881851415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26472488296140611842468553 19854366222105458881851415)
              ·
                refine ⟨29781549333158188322777123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19854366222105458881851415 29781549333158188322777123)
                ·
                  refine ⟨44672323999737282484165685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29781549333158188322777123 44672323999737282484165685)
                  ·
                    refine ⟨4188030374975370232890533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44672323999737282484165685 4188030374975370232890533)
                    ·
                      refine ⟨785255695307881918666975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4188030374975370232890533 785255695307881918666975)
                      ·
                        rfl

theorem cell23_1529280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1529280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529280 prefixEnd_1529280 := by exact prefixLift 1529280
  have htrace : WordTrace (prefixWord ++ tailWord_1529280) baseStart_1529280 baseEnd_1529280 := by
    simpa [prefixWord, tailWord_1529280, baseEnd_1529280] using wordTrace_append hprefix tailTrace_1529280
  have hstable : (prefixWord ++ tailWord_1529280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529280).length < 2 ^ (prefixWord ++ tailWord_1529280).sum := by decide
  have hdescent : baseEnd_1529280 < baseStart_1529280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529301 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1529301 : Nat := 118140960795 + 1529301 * 2 ^ 59
def prefixEnd_1529301 : Nat := 4983230072969 + 3 ^ 40 * 1529301 * 2
def baseEnd_1529301 : Nat := 785266478401626336504379

theorem tailTrace_1529301 : CollatzResearch.WordTrace tailWord_1529301 prefixEnd_1529301 785266478401626336504379 := by
  unfold tailWord_1529301
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778189832611135662003757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37185459888407423774669171 55778189832611135662003757)
  ·
    refine ⟨20916821187229175873251409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55778189832611135662003757 20916821187229175873251409)
    ·
      refine ⟨15687615890421881904938557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20916821187229175873251409 15687615890421881904938557)
      ·
        refine ⟨5882855958908205714351959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15687615890421881904938557 5882855958908205714351959)
        ·
          refine ⟨8824283938362308571527939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882855958908205714351959 8824283938362308571527939)
          ·
            refine ⟨13236425907543462857291909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824283938362308571527939 13236425907543462857291909)
            ·
              refine ⟨2481829857664399285742233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13236425907543462857291909 2481829857664399285742233)
              ·
                refine ⟨1861372393248299464306675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481829857664399285742233 1861372393248299464306675)
                ·
                  refine ⟨2792058589872449196460013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861372393248299464306675 2792058589872449196460013)
                  ·
                    refine ⟨1047021971202168448672505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2792058589872449196460013 1047021971202168448672505)
                    ·
                      refine ⟨785266478401626336504379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047021971202168448672505 785266478401626336504379)
                      ·
                        rfl

theorem cell23_1529301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1529301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529301 prefixEnd_1529301 := by exact prefixLift 1529301
  have htrace : WordTrace (prefixWord ++ tailWord_1529301) baseStart_1529301 baseEnd_1529301 := by
    simpa [prefixWord, tailWord_1529301, baseEnd_1529301] using wordTrace_append hprefix tailTrace_1529301
  have hstable : (prefixWord ++ tailWord_1529301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529301).length < 2 ^ (prefixWord ++ tailWord_1529301).sum := by decide
  have hdescent : baseEnd_1529301 < baseStart_1529301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529317 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1529317 : Nat := 118140960795 + 1529317 * 2 ^ 59
def prefixEnd_1529317 : Nat := 4983230072969 + 3 ^ 40 * 1529317 * 2
def baseEnd_1529317 : Nat := 785274694092098273904305

theorem tailTrace_1529317 : CollatzResearch.WordTrace tailWord_1529317 prefixEnd_1529317 785274694092098273904305 := by
  unfold tailWord_1529317
  simp only [CollatzResearch.WordTrace]
  refine ⟨55778773400553170394586205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37185848933702113596390803 55778773400553170394586205)
  ·
    refine ⟨20917040025207438897969827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55778773400553170394586205 20917040025207438897969827)
    ·
      refine ⟨31375560037811158346954741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20917040025207438897969827 31375560037811158346954741)
      ·
        refine ⟨2941458753544796095027007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31375560037811158346954741 2941458753544796095027007)
        ·
          refine ⟨4412188130317194142540511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941458753544796095027007 4412188130317194142540511)
          ·
            refine ⟨6618282195475791213810767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412188130317194142540511 6618282195475791213810767)
            ·
              refine ⟨9927423293213686820716151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618282195475791213810767 9927423293213686820716151)
              ·
                refine ⟨14891134939820530231074227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927423293213686820716151 14891134939820530231074227)
                ·
                  refine ⟨22336702409730795346611341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14891134939820530231074227 22336702409730795346611341)
                  ·
                    refine ⟨8376263403649048254979253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22336702409730795346611341 8376263403649048254979253)
                    ·
                      refine ⟨785274694092098273904305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8376263403649048254979253 785274694092098273904305)
                      ·
                        rfl

theorem cell23_1529317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1529317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529317 prefixEnd_1529317 := by exact prefixLift 1529317
  have htrace : WordTrace (prefixWord ++ tailWord_1529317) baseStart_1529317 baseEnd_1529317 := by
    simpa [prefixWord, tailWord_1529317, baseEnd_1529317] using wordTrace_append hprefix tailTrace_1529317
  have hstable : (prefixWord ++ tailWord_1529317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529317).length < 2 ^ (prefixWord ++ tailWord_1529317).sum := by decide
  have hdescent : baseEnd_1529317 < baseStart_1529317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529342 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1529342 : Nat := 118140960795 + 1529342 * 2 ^ 59
def prefixEnd_1529342 : Nat := 4983230072969 + 3 ^ 40 * 1529342 * 2
def baseEnd_1529342 : Nat := 785287531108460676091691

theorem tailTrace_1529342 : CollatzResearch.WordTrace tailWord_1529342 prefixEnd_1529342 785287531108460676091691 := by
  unfold tailWord_1529342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972460653182824958030785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37186456816975066442830853 6972460653182824958030785)
  ·
    refine ⟨5229345489887118718523089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6972460653182824958030785 5229345489887118718523089)
    ·
      refine ⟨3922009117415339038892317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5229345489887118718523089 3922009117415339038892317)
      ·
        refine ⟨1470753419030752139584619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3922009117415339038892317 1470753419030752139584619)
        ·
          refine ⟨2206130128546128209376929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470753419030752139584619 2206130128546128209376929)
          ·
            refine ⟨1654597596409596157032697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206130128546128209376929 1654597596409596157032697)
            ·
              refine ⟨1240948197307197117774523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654597596409596157032697 1240948197307197117774523)
              ·
                refine ⟨1861422295960795676661785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240948197307197117774523 1861422295960795676661785)
                ·
                  refine ⟨1396066721970596757496339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861422295960795676661785 1396066721970596757496339)
                  ·
                    refine ⟨2094100082955895136244509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1396066721970596757496339 2094100082955895136244509)
                    ·
                      refine ⟨785287531108460676091691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2094100082955895136244509 785287531108460676091691)
                      ·
                        rfl

theorem cell23_1529342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1529342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529342 prefixEnd_1529342 := by exact prefixLift 1529342
  have htrace : WordTrace (prefixWord ++ tailWord_1529342) baseStart_1529342 baseEnd_1529342 := by
    simpa [prefixWord, tailWord_1529342, baseEnd_1529342] using wordTrace_append hprefix tailTrace_1529342
  have hstable : (prefixWord ++ tailWord_1529342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529342).length < 2 ^ (prefixWord ++ tailWord_1529342).sum := by decide
  have hdescent : baseEnd_1529342 < baseStart_1529342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529377 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1529377 : Nat := 118140960795 + 1529377 * 2 ^ 59
def prefixEnd_1529377 : Nat := 4983230072969 + 3 ^ 40 * 1529377 * 2
def baseEnd_1529377 : Nat := 785305502931368039154029

theorem tailTrace_1529377 : CollatzResearch.WordTrace tailWord_1529377 prefixEnd_1529377 785305502931368039154029 := by
  unfold tailWord_1529377
  simp only [CollatzResearch.WordTrace]
  refine ⟨55780961780335800641770385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37187307853557200427846923 55780961780335800641770385)
  ·
    refine ⟨41835721335251850481327789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55780961780335800641770385 41835721335251850481327789)
    ·
      refine ⟨15688395500719443930497921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41835721335251850481327789 15688395500719443930497921)
      ·
        refine ⟨11766296625539582947873441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15688395500719443930497921 11766296625539582947873441)
        ·
          refine ⟨8824722469154687210905081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11766296625539582947873441 8824722469154687210905081)
          ·
            refine ⟨6618541851866015408178811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824722469154687210905081 6618541851866015408178811)
            ·
              refine ⟨9927812777799023112268217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618541851866015408178811 9927812777799023112268217)
              ·
                refine ⟨7445859583349267334201163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927812777799023112268217 7445859583349267334201163)
                ·
                  refine ⟨11168789375023901001301745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7445859583349267334201163 11168789375023901001301745)
                  ·
                    refine ⟨8376592031267925750976309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11168789375023901001301745 8376592031267925750976309)
                    ·
                      refine ⟨785305502931368039154029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8376592031267925750976309 785305502931368039154029)
                      ·
                        rfl

theorem cell23_1529377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1529377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529377 prefixEnd_1529377 := by exact prefixLift 1529377
  have htrace : WordTrace (prefixWord ++ tailWord_1529377) baseStart_1529377 baseEnd_1529377 := by
    simpa [prefixWord, tailWord_1529377, baseEnd_1529377] using wordTrace_append hprefix tailTrace_1529377
  have hstable : (prefixWord ++ tailWord_1529377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529377).length < 2 ^ (prefixWord ++ tailWord_1529377).sum := by decide
  have hdescent : baseEnd_1529377 < baseStart_1529377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529421 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1529421 : Nat := 118140960795 + 1529421 * 2 ^ 59
def prefixEnd_1529421 : Nat := 4983230072969 + 3 ^ 40 * 1529421 * 2
def baseEnd_1529421 : Nat := 785328096080165867003827

theorem tailTrace_1529421 : CollatzResearch.WordTrace tailWord_1529421 prefixEnd_1529421 785328096080165867003827 := by
  unfold tailWord_1529421
  simp only [CollatzResearch.WordTrace]
  refine ⟨55782566592176396156372117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37188377728117597437581411 55782566592176396156372117)
  ·
    refine ⟨2614807809008268569829943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55782566592176396156372117 2614807809008268569829943)
    ·
      refine ⟨3922211713512402854744915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614807809008268569829943 3922211713512402854744915)
      ·
        refine ⟨5883317570268604282117373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922211713512402854744915 5883317570268604282117373)
        ·
          refine ⟨2206244088850726605794015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5883317570268604282117373 2206244088850726605794015)
          ·
            refine ⟨3309366133276089908691023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206244088850726605794015 3309366133276089908691023)
            ·
              refine ⟨4964049199914134863036535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309366133276089908691023 4964049199914134863036535)
              ·
                refine ⟨7446073799871202294554803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964049199914134863036535 7446073799871202294554803)
                ·
                  refine ⟨11169110699806803441832205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7446073799871202294554803 11169110699806803441832205)
                  ·
                    refine ⟨4188416512427551290687077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11169110699806803441832205 4188416512427551290687077)
                    ·
                      refine ⟨785328096080165867003827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4188416512427551290687077 785328096080165867003827)
                      ·
                        rfl

theorem cell23_1529421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1529421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529421 prefixEnd_1529421 := by exact prefixLift 1529421
  have htrace : WordTrace (prefixWord ++ tailWord_1529421) baseStart_1529421 baseEnd_1529421 := by
    simpa [prefixWord, tailWord_1529421, baseEnd_1529421] using wordTrace_append hprefix tailTrace_1529421
  have hstable : (prefixWord ++ tailWord_1529421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529421).length < 2 ^ (prefixWord ++ tailWord_1529421).sum := by decide
  have hdescent : baseEnd_1529421 < baseStart_1529421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529431 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 1, 4]
def baseStart_1529431 : Nat := 118140960795 + 1529431 * 2 ^ 59
def prefixEnd_1529431 : Nat := 4983230072969 + 3 ^ 40 * 1529431 * 2
def baseEnd_1529431 : Nat := 261777743628903609292927

theorem tailTrace_1529431 : CollatzResearch.WordTrace tailWord_1529431 prefixEnd_1529431 261777743628903609292927 := by
  unfold tailWord_1529431
  simp only [CollatzResearch.WordTrace]
  refine ⟨55782931322140167864236147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37188620881426778576157431 55782931322140167864236147)
  ·
    refine ⟨83674396983210251796354221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55782931322140167864236147 83674396983210251796354221)
    ·
      refine ⟨31377898868703844423632833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83674396983210251796354221 31377898868703844423632833)
      ·
        refine ⟨23533424151527883317724625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31377898868703844423632833 23533424151527883317724625)
        ·
          refine ⟨17650068113645912488293469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23533424151527883317724625 17650068113645912488293469)
          ·
            refine ⟨6618775542617217183110051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17650068113645912488293469 6618775542617217183110051)
            ·
              refine ⟨9928163313925825774665077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618775542617217183110051 9928163313925825774665077)
              ·
                refine ⟨930765310680546166374851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9928163313925825774665077 930765310680546166374851)
                ·
                  refine ⟨1396147966020819249562277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930765310680546166374851 1396147966020819249562277)
                  ·
                    refine ⟨261777743628903609292927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396147966020819249562277 261777743628903609292927)
                    ·
                      rfl

theorem cell23_1529431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_1529431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529431 prefixEnd_1529431 := by exact prefixLift 1529431
  have htrace : WordTrace (prefixWord ++ tailWord_1529431) baseStart_1529431 baseEnd_1529431 := by
    simpa [prefixWord, tailWord_1529431, baseEnd_1529431] using wordTrace_append hprefix tailTrace_1529431
  have hstable : (prefixWord ++ tailWord_1529431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529431).length < 2 ^ (prefixWord ++ tailWord_1529431).sum := by decide
  have hdescent : baseEnd_1529431 < baseStart_1529431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529444 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1529444 : Nat := 118140960795 + 1529444 * 2 ^ 59
def prefixEnd_1529444 : Nat := 4983230072969 + 3 ^ 40 * 1529444 * 2
def baseEnd_1529444 : Nat := 87259989570579919668469

theorem tailTrace_1529444 : CollatzResearch.WordTrace tailWord_1529444 prefixEnd_1529444 87259989570579919668469 := by
  unfold tailWord_1529444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27891702735546535542229693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37188936980728714056306257 27891702735546535542229693)
  ·
    refine ⟨10459388525829950828336135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27891702735546535542229693 10459388525829950828336135)
    ·
      refine ⟨15689082788744926242504203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459388525829950828336135 15689082788744926242504203)
      ·
        refine ⟨23533624183117389363756305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689082788744926242504203 23533624183117389363756305)
        ·
          refine ⟨17650218137338042022817229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23533624183117389363756305 17650218137338042022817229)
          ·
            refine ⟨6618831801501765758556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17650218137338042022817229 6618831801501765758556461)
            ·
              refine ⟨2482061925563162159458673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6618831801501765758556461 2482061925563162159458673)
              ·
                refine ⟨1861546444172371619594005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482061925563162159458673 1861546444172371619594005)
                ·
                  refine ⟨87259989570579919668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861546444172371619594005 87259989570579919668469)
                  ·
                    rfl

theorem cell23_1529444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1529444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529444 prefixEnd_1529444 := by exact prefixLift 1529444
  have htrace : WordTrace (prefixWord ++ tailWord_1529444) baseStart_1529444 baseEnd_1529444 := by
    simpa [prefixWord, tailWord_1529444, baseEnd_1529444] using wordTrace_append hprefix tailTrace_1529444
  have hstable : (prefixWord ++ tailWord_1529444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529444).length < 2 ^ (prefixWord ++ tailWord_1529444).sum := by decide
  have hdescent : baseEnd_1529444 < baseStart_1529444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529447 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1529447 : Nat := 118140960795 + 1529447 * 2 ^ 59
def prefixEnd_1529447 : Nat := 4983230072969 + 3 ^ 40 * 1529447 * 2
def baseEnd_1529447 : Nat := 785341446577182765278707

theorem tailTrace_1529447 : CollatzResearch.WordTrace tailWord_1529447 prefixEnd_1529447 785341446577182765278707 := by
  unfold tailWord_1529447
  simp only [CollatzResearch.WordTrace]
  refine ⟨55783514890082202596818595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37189009926721468397879063 55783514890082202596818595)
  ·
    refine ⟨83675272335123303895227893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55783514890082202596818595 83675272335123303895227893)
    ·
      refine ⟨7844556781417809740177615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83675272335123303895227893 7844556781417809740177615)
      ·
        refine ⟨11766835172126714610266423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7844556781417809740177615 11766835172126714610266423)
        ·
          refine ⟨17650252758190071915399635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11766835172126714610266423 17650252758190071915399635)
          ·
            refine ⟨26475379137285107873099453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17650252758190071915399635 26475379137285107873099453)
            ·
              refine ⟨9928267176481915452412295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26475379137285107873099453 9928267176481915452412295)
              ·
                refine ⟨14892400764722873178618443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928267176481915452412295 14892400764722873178618443)
                ·
                  refine ⟨22338601147084309767927665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14892400764722873178618443 22338601147084309767927665)
                  ·
                    refine ⟨16753950860313232325945749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22338601147084309767927665 16753950860313232325945749)
                    ·
                      refine ⟨785341446577182765278707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16753950860313232325945749 785341446577182765278707)
                      ·
                        rfl

theorem cell23_1529447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1529447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529447 prefixEnd_1529447 := by exact prefixLift 1529447
  have htrace : WordTrace (prefixWord ++ tailWord_1529447) baseStart_1529447 baseEnd_1529447 := by
    simpa [prefixWord, tailWord_1529447, baseEnd_1529447] using wordTrace_append hprefix tailTrace_1529447
  have hstable : (prefixWord ++ tailWord_1529447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529447).length < 2 ^ (prefixWord ++ tailWord_1529447).sum := by decide
  have hdescent : baseEnd_1529447 < baseStart_1529447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529448 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1529448 : Nat := 118140960795 + 1529448 * 2 ^ 59
def prefixEnd_1529448 : Nat := 4983230072969 + 3 ^ 40 * 1529448 * 2
def baseEnd_1529448 : Nat := 261780653352612420455401

theorem tailTrace_1529448 : CollatzResearch.WordTrace tailWord_1529448 prefixEnd_1529448 261780653352612420455401 := by
  unfold tailWord_1529448
  simp only [CollatzResearch.WordTrace]
  refine ⟨27891775681539289883802499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37189034242052386511736665 27891775681539289883802499)
  ·
    refine ⟨41837663522308934825703749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27891775681539289883802499 41837663522308934825703749)
    ·
      refine ⟨7844561910432925279819453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41837663522308934825703749 7844561910432925279819453)
      ·
        refine ⟨2941710716412346979932295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7844561910432925279819453 2941710716412346979932295)
        ·
          refine ⟨4412566074618520469898443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941710716412346979932295 4412566074618520469898443)
          ·
            refine ⟨6618849111927780704847665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4412566074618520469898443 6618849111927780704847665)
            ·
              refine ⟨4964136833945835528635749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6618849111927780704847665 4964136833945835528635749)
              ·
                refine ⟨930775656364844161619203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4964136833945835528635749 930775656364844161619203)
                ·
                  refine ⟨1396163484547266242428805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930775656364844161619203 1396163484547266242428805)
                  ·
                    refine ⟨261780653352612420455401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396163484547266242428805 261780653352612420455401)
                    ·
                      rfl

theorem cell23_1529448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1529448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529448 prefixEnd_1529448 := by exact prefixLift 1529448
  have htrace : WordTrace (prefixWord ++ tailWord_1529448) baseStart_1529448 baseEnd_1529448 := by
    simpa [prefixWord, tailWord_1529448, baseEnd_1529448] using wordTrace_append hprefix tailTrace_1529448
  have hstable : (prefixWord ++ tailWord_1529448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529448).length < 2 ^ (prefixWord ++ tailWord_1529448).sum := by decide
  have hdescent : baseEnd_1529448 < baseStart_1529448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529457 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1529457 : Nat := 118140960795 + 1529457 * 2 ^ 59
def prefixEnd_1529457 : Nat := 4983230072969 + 3 ^ 40 * 1529457 * 2
def baseEnd_1529457 : Nat := 261782193794575908717887

theorem tailTrace_1529457 : CollatzResearch.WordTrace tailWord_1529457 prefixEnd_1529457 261782193794575908717887 := by
  unfold tailWord_1529457
  simp only [CollatzResearch.WordTrace]
  refine ⟨55783879620045974304682625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37189253080030649536455083 55783879620045974304682625)
  ·
    refine ⟨41837909715034480728511969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55783879620045974304682625 41837909715034480728511969)
    ·
      refine ⟨31378432286275860546383977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41837909715034480728511969 31378432286275860546383977)
      ·
        refine ⟨23533824214706895409787983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31378432286275860546383977 23533824214706895409787983)
        ·
          refine ⟨35300736322060343114681975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23533824214706895409787983 35300736322060343114681975)
          ·
            refine ⟨52951104483090514672022963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35300736322060343114681975 52951104483090514672022963)
            ·
              refine ⟨79426656724635772008034445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52951104483090514672022963 79426656724635772008034445)
              ·
                refine ⟨29784996271738414503012917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79426656724635772008034445 29784996271738414503012917)
                ·
                  refine ⟨2792343400475476359657461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29784996271738414503012917 2792343400475476359657461)
                  ·
                    refine ⟨261782193794575908717887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2792343400475476359657461 261782193794575908717887)
                    ·
                      rfl

theorem cell23_1529457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1529457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529457 prefixEnd_1529457 := by exact prefixLift 1529457
  have htrace : WordTrace (prefixWord ++ tailWord_1529457) baseStart_1529457 baseEnd_1529457 := by
    simpa [prefixWord, tailWord_1529457, baseEnd_1529457] using wordTrace_append hprefix tailTrace_1529457
  have hstable : (prefixWord ++ tailWord_1529457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529457).length < 2 ^ (prefixWord ++ tailWord_1529457).sum := by decide
  have hdescent : baseEnd_1529457 < baseStart_1529457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529507 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1529507 : Nat := 118140960795 + 1529507 * 2 ^ 59
def prefixEnd_1529507 : Nat := 4983230072969 + 3 ^ 40 * 1529507 * 2
def baseEnd_1529507 : Nat := 785372255416452530528431

theorem tailTrace_1529507 : CollatzResearch.WordTrace tailWord_1529507 prefixEnd_1529507 785372255416452530528431 := by
  unfold tailWord_1529507
  simp only [CollatzResearch.WordTrace]
  refine ⟨55785703269864832844002775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37190468846576555229335183 55785703269864832844002775)
  ·
    refine ⟨83678554904797249266004163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55785703269864832844002775 83678554904797249266004163)
    ·
      refine ⟨125517832357195873899006245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83678554904797249266004163 125517832357195873899006245)
      ·
        refine ⟨23534593566974226356063671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125517832357195873899006245 23534593566974226356063671)
        ·
          refine ⟨35301890350461339534095507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23534593566974226356063671 35301890350461339534095507)
          ·
            refine ⟨52952835525692009301143261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35301890350461339534095507 52952835525692009301143261)
            ·
              refine ⟨19857313322134503487928723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52952835525692009301143261 19857313322134503487928723)
              ·
                refine ⟨29785969983201755231893085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19857313322134503487928723 29785969983201755231893085)
                ·
                  refine ⟨11169738743700658211959907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29785969983201755231893085 11169738743700658211959907)
                  ·
                    refine ⟨16754608115550987317939861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11169738743700658211959907 16754608115550987317939861)
                    ·
                      refine ⟨785372255416452530528431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16754608115550987317939861 785372255416452530528431)
                      ·
                        rfl

theorem cell23_1529507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1529507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529507 prefixEnd_1529507 := by exact prefixLift 1529507
  have htrace : WordTrace (prefixWord ++ tailWord_1529507) baseStart_1529507 baseEnd_1529507 := by
    simpa [prefixWord, tailWord_1529507, baseEnd_1529507] using wordTrace_append hprefix tailTrace_1529507
  have hstable : (prefixWord ++ tailWord_1529507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529507).length < 2 ^ (prefixWord ++ tailWord_1529507).sum := by decide
  have hdescent : baseEnd_1529507 < baseStart_1529507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529512 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 6]
def baseStart_1529512 : Nat := 118140960795 + 1529512 * 2 ^ 59
def prefixEnd_1529512 : Nat := 4983230072969 + 3 ^ 40 * 1529512 * 2
def baseEnd_1529512 : Nat := 87263869202191667885101

theorem tailTrace_1529512 : CollatzResearch.WordTrace tailWord_1529512 prefixEnd_1529512 87263869202191667885101 := by
  unfold tailWord_1529512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892942817423359348967395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37190590423231145798623193 27892942817423359348967395)
  ·
    refine ⟨41839414226135039023451093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27892942817423359348967395 41839414226135039023451093)
    ·
      refine ⟨980611270925039977112135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41839414226135039023451093 980611270925039977112135)
      ·
        refine ⟨1470916906387559965668203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980611270925039977112135 1470916906387559965668203)
        ·
          refine ⟨2206375359581339948502305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470916906387559965668203 2206375359581339948502305)
          ·
            refine ⟨1654781519686004961376729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206375359581339948502305 1654781519686004961376729)
            ·
              refine ⟨1241086139764503721032547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654781519686004961376729 1241086139764503721032547)
              ·
                refine ⟨1861629209646755581548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241086139764503721032547 1861629209646755581548821)
                ·
                  refine ⟨87263869202191667885101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861629209646755581548821 87263869202191667885101)
                  ·
                    rfl

theorem cell23_1529512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 6].length) (baseStart_1529512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529512 prefixEnd_1529512 := by exact prefixLift 1529512
  have htrace : WordTrace (prefixWord ++ tailWord_1529512) baseStart_1529512 baseEnd_1529512 := by
    simpa [prefixWord, tailWord_1529512, baseEnd_1529512] using wordTrace_append hprefix tailTrace_1529512
  have hstable : (prefixWord ++ tailWord_1529512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529512).length < 2 ^ (prefixWord ++ tailWord_1529512).sum := by decide
  have hdescent : baseEnd_1529512 < baseStart_1529512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529525 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1529525 : Nat := 118140960795 + 1529525 * 2 ^ 59
def prefixEnd_1529525 : Nat := 4983230072969 + 3 ^ 40 * 1529525 * 2
def baseEnd_1529525 : Nat := 261793832689411153367783

theorem tailTrace_1529525 : CollatzResearch.WordTrace tailWord_1529525 prefixEnd_1529525 261793832689411153367783 := by
  unfold tailWord_1529525
  simp only [CollatzResearch.WordTrace]
  refine ⟨55786359783799621918158029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37190906522533081278772019 55786359783799621918158029)
  ·
    refine ⟨20919884918924858219309261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55786359783799621918158029 20919884918924858219309261)
    ·
      refine ⟨7844956844596821832240973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20919884918924858219309261 7844956844596821832240973)
      ·
        refine ⟨2941858816723808187090365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7844956844596821832240973 2941858816723808187090365)
        ·
          refine ⟨1103197056271428070158887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2941858816723808187090365 1103197056271428070158887)
          ·
            refine ⟨1654795584407142105238331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103197056271428070158887 1654795584407142105238331)
            ·
              refine ⟨2482193376610713157857497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654795584407142105238331 2482193376610713157857497)
              ·
                refine ⟨1861645032458034868393123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482193376610713157857497 1861645032458034868393123)
                ·
                  refine ⟨2792467548687052302589685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861645032458034868393123 2792467548687052302589685)
                  ·
                    refine ⟨261793832689411153367783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2792467548687052302589685 261793832689411153367783)
                    ·
                      rfl

theorem cell23_1529525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1529525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529525 prefixEnd_1529525 := by exact prefixLift 1529525
  have htrace : WordTrace (prefixWord ++ tailWord_1529525) baseStart_1529525 baseEnd_1529525 := by
    simpa [prefixWord, tailWord_1529525, baseEnd_1529525] using wordTrace_append hprefix tailTrace_1529525
  have hstable : (prefixWord ++ tailWord_1529525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529525).length < 2 ^ (prefixWord ++ tailWord_1529525).sum := by decide
  have hdescent : baseEnd_1529525 < baseStart_1529525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529534 : List Nat := [4, 2, 1, 1, 2, 2, 2, 9]
def baseStart_1529534 : Nat := 118140960795 + 1529534 * 2 ^ 59
def prefixEnd_1529534 : Nat := 4983230072969 + 3 ^ 40 * 1529534 * 2
def baseEnd_1529534 : Nat := 29088374792374960181141

theorem tailTrace_1529534 : CollatzResearch.WordTrace tailWord_1529534 prefixEnd_1529534 29088374792374960181141 := by
  unfold tailWord_1529534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973336005095877056904457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37191125360511344303490437 6973336005095877056904457)
  ·
    refine ⟨5230002003821907792678343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6973336005095877056904457 5230002003821907792678343)
    ·
      refine ⟨7845003005732861689017515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230002003821907792678343 7845003005732861689017515)
      ·
        refine ⟨11767504508599292533526273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7845003005732861689017515 11767504508599292533526273)
        ·
          refine ⟨8825628381449469400144705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11767504508599292533526273 8825628381449469400144705)
          ·
            refine ⟨6619221286087102050108529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8825628381449469400144705 6619221286087102050108529)
            ·
              refine ⟨4964415964565326537581397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6619221286087102050108529 4964415964565326537581397)
              ·
                refine ⟨29088374792374960181141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4964415964565326537581397 29088374792374960181141)
                ·
                  rfl

theorem cell23_1529534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_1529534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529534 prefixEnd_1529534 := by exact prefixLift 1529534
  have htrace : WordTrace (prefixWord ++ tailWord_1529534) baseStart_1529534 baseEnd_1529534 := by
    simpa [prefixWord, tailWord_1529534, baseEnd_1529534] using wordTrace_append hprefix tailTrace_1529534
  have hstable : (prefixWord ++ tailWord_1529534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529534).length < 2 ^ (prefixWord ++ tailWord_1529534).sum := by decide
  have hdescent : baseEnd_1529534 < baseStart_1529534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529542 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1529542 : Nat := 118140960795 + 1529542 * 2 ^ 59
def prefixEnd_1529542 : Nat := 4983230072969 + 3 ^ 40 * 1529542 * 2
def baseEnd_1529542 : Nat := 261796742413119964530257

theorem tailTrace_1529542 : CollatzResearch.WordTrace tailWord_1529542 prefixEnd_1529542 261796742413119964530257 := by
  unfold tailWord_1529542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743343119523063556922715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37191319883158689214351253 1743343119523063556922715)
  ·
    refine ⟨2615014679284595335384073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743343119523063556922715 2615014679284595335384073)
    ·
      refine ⟨1961261009463446501538055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2615014679284595335384073 1961261009463446501538055)
      ·
        refine ⟨2941891514195169752307083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961261009463446501538055 2941891514195169752307083)
        ·
          refine ⟨4412837271292754628460625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941891514195169752307083 4412837271292754628460625)
          ·
            refine ⟨3309627953469565971345469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412837271292754628460625 3309627953469565971345469)
            ·
              refine ⟨1241110482551087239254551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3309627953469565971345469 1241110482551087239254551)
              ·
                refine ⟨1861665723826630858881827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241110482551087239254551 1861665723826630858881827)
                ·
                  refine ⟨2792498585739946288322741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861665723826630858881827 2792498585739946288322741)
                  ·
                    refine ⟨261796742413119964530257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2792498585739946288322741 261796742413119964530257)
                    ·
                      rfl

theorem cell23_1529542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1529542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529542 prefixEnd_1529542 := by exact prefixLift 1529542
  have htrace : WordTrace (prefixWord ++ tailWord_1529542) baseStart_1529542 baseEnd_1529542 := by
    simpa [prefixWord, tailWord_1529542, baseEnd_1529542] using wordTrace_append hprefix tailTrace_1529542
  have hstable : (prefixWord ++ tailWord_1529542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529542).length < 2 ^ (prefixWord ++ tailWord_1529542).sum := by decide
  have hdescent : baseEnd_1529542 < baseStart_1529542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529547 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 7]
def baseStart_1529547 : Nat := 118140960795 + 1529547 * 2 ^ 59
def prefixEnd_1529547 : Nat := 4983230072969 + 3 ^ 40 * 1529547 * 2
def baseEnd_1529547 : Nat := 261797598214210791342749

theorem tailTrace_1529547 : CollatzResearch.WordTrace tailWord_1529547 prefixEnd_1529547 261797598214210791342749 := by
  unfold tailWord_1529547
  simp only [CollatzResearch.WordTrace]
  refine ⟨55787162189719919675458895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37191441459813279783639263 55787162189719919675458895)
  ·
    refine ⟨83680743284579879513188343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55787162189719919675458895 83680743284579879513188343)
    ·
      refine ⟨125521114926869819269782515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83680743284579879513188343 125521114926869819269782515)
      ·
        refine ⟨188281672390304728904673773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125521114926869819269782515 188281672390304728904673773)
        ·
          refine ⟨70605627146364273339252665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188281672390304728904673773 70605627146364273339252665)
          ·
            refine ⟨52954220359773205004439499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70605627146364273339252665 52954220359773205004439499)
            ·
              refine ⟨79431330539659807506659249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52954220359773205004439499 79431330539659807506659249)
              ·
                refine ⟨59573497904744855629994437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79431330539659807506659249 59573497904744855629994437)
                ·
                  refine ⟨11170030857139660430623957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59573497904744855629994437 11170030857139660430623957)
                  ·
                    refine ⟨261797598214210791342749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11170030857139660430623957 261797598214210791342749)
                    ·
                      rfl

theorem cell23_1529547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_1529547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529547 prefixEnd_1529547 := by exact prefixLift 1529547
  have htrace : WordTrace (prefixWord ++ tailWord_1529547) baseStart_1529547 baseEnd_1529547 := by
    simpa [prefixWord, tailWord_1529547, baseEnd_1529547] using wordTrace_append hprefix tailTrace_1529547
  have hstable : (prefixWord ++ tailWord_1529547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529547).length < 2 ^ (prefixWord ++ tailWord_1529547).sum := by decide
  have hdescent : baseEnd_1529547 < baseStart_1529547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529548 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1529548 : Nat := 118140960795 + 1529548 * 2 ^ 59
def prefixEnd_1529548 : Nat := 4983230072969 + 3 ^ 40 * 1529548 * 2
def baseEnd_1529548 : Nat := 785393308123286870115743

theorem tailTrace_1529548 : CollatzResearch.WordTrace tailWord_1529548 prefixEnd_1529548 785393308123286870115743 := by
  unfold tailWord_1529548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27893599331358148423122649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37191465775144197897496865 27893599331358148423122649)
  ·
    refine ⟨20920199498518611317341987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27893599331358148423122649 20920199498518611317341987)
    ·
      refine ⟨31380299247777916976012981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20920199498518611317341987 31380299247777916976012981)
      ·
        refine ⟨2941903054479179716501217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31380299247777916976012981 2941903054479179716501217)
        ·
          refine ⟨2206427290859384787375913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941903054479179716501217 2206427290859384787375913)
          ·
            refine ⟨1654820468144538590531935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206427290859384787375913 1654820468144538590531935)
            ·
              refine ⟨2482230702216807885797903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654820468144538590531935 2482230702216807885797903)
              ·
                refine ⟨3723346053325211828696855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482230702216807885797903 3723346053325211828696855)
                ·
                  refine ⟨5585019079987817743045283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723346053325211828696855 5585019079987817743045283)
                  ·
                    refine ⟨8377528619981726614567925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585019079987817743045283 8377528619981726614567925)
                    ·
                      refine ⟨785393308123286870115743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8377528619981726614567925 785393308123286870115743)
                      ·
                        rfl

theorem cell23_1529548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1529548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529548 prefixEnd_1529548 := by exact prefixLift 1529548
  have htrace : WordTrace (prefixWord ++ tailWord_1529548) baseStart_1529548 baseEnd_1529548 := by
    simpa [prefixWord, tailWord_1529548, baseEnd_1529548] using wordTrace_append hprefix tailTrace_1529548
  have hstable : (prefixWord ++ tailWord_1529548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529548).length < 2 ^ (prefixWord ++ tailWord_1529548).sum := by decide
  have hdescent : baseEnd_1529548 < baseStart_1529548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529562 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_1529562 : Nat := 118140960795 + 1529562 * 2 ^ 59
def prefixEnd_1529562 : Nat := 4983230072969 + 3 ^ 40 * 1529562 * 2
def baseEnd_1529562 : Nat := 785400496852449815340679

theorem tailTrace_1529562 : CollatzResearch.WordTrace tailWord_1529562 prefixEnd_1529562 785400496852449815340679 := by
  unfold tailWord_1529562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13946927321166394309313735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37191806189777051491503293 13946927321166394309313735)
  ·
    refine ⟨20920390981749591463970603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13946927321166394309313735 20920390981749591463970603)
    ·
      refine ⟨31380586472624387195955905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20920390981749591463970603 31380586472624387195955905)
      ·
        refine ⟨23535439854468290396966929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31380586472624387195955905 23535439854468290396966929)
        ·
          refine ⟨17651579890851217797725197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23535439854468290396966929 17651579890851217797725197)
          ·
            refine ⟨6619342459069206674146949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17651579890851217797725197 6619342459069206674146949)
            ·
              refine ⟨1241126711075476251402553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6619342459069206674146949 1241126711075476251402553)
              ·
                refine ⟨930845033306607188551915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241126711075476251402553 930845033306607188551915)
                ·
                  refine ⟨1396267549959910782827873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930845033306607188551915 1396267549959910782827873)
                  ·
                    refine ⟨1047200662469933087120905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396267549959910782827873 1047200662469933087120905)
                    ·
                      refine ⟨785400496852449815340679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047200662469933087120905 785400496852449815340679)
                      ·
                        rfl

theorem cell23_1529562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_1529562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529562 prefixEnd_1529562 := by exact prefixLift 1529562
  have htrace : WordTrace (prefixWord ++ tailWord_1529562) baseStart_1529562 baseEnd_1529562 := by
    simpa [prefixWord, tailWord_1529562, baseEnd_1529562] using wordTrace_append hprefix tailTrace_1529562
  have hstable : (prefixWord ++ tailWord_1529562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529562).length < 2 ^ (prefixWord ++ tailWord_1529562).sum := by decide
  have hdescent : baseEnd_1529562 < baseStart_1529562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529578 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1529578 : Nat := 118140960795 + 1529578 * 2 ^ 59
def prefixEnd_1529578 : Nat := 4983230072969 + 3 ^ 40 * 1529578 * 2
def baseEnd_1529578 : Nat := 785408712542921752740605

theorem tailTrace_1529578 : CollatzResearch.WordTrace tailWord_1529578 prefixEnd_1529578 785408712542921752740605 := by
  unfold tailWord_1529578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947073213151902992459347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37192195235071741313224925 13947073213151902992459347)
  ·
    refine ⟨20920609819727854488689021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13947073213151902992459347 20920609819727854488689021)
    ·
      refine ⟨7845228682397945433258383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20920609819727854488689021 7845228682397945433258383)
      ·
        refine ⟨11767843023596918149887575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7845228682397945433258383 11767843023596918149887575)
        ·
          refine ⟨17651764535395377224831363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11767843023596918149887575 17651764535395377224831363)
          ·
            refine ⟨26477646803093065837247045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17651764535395377224831363 26477646803093065837247045)
            ·
              refine ⟨4964558775579949844483821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26477646803093065837247045 4964558775579949844483821)
              ·
                refine ⟨1861709540842481191681433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4964558775579949844483821 1861709540842481191681433)
                ·
                  refine ⟨1396282155631860893761075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861709540842481191681433 1396282155631860893761075)
                  ·
                    refine ⟨2094423233447791340641613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1396282155631860893761075 2094423233447791340641613)
                    ·
                      refine ⟨785408712542921752740605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2094423233447791340641613 785408712542921752740605)
                      ·
                        rfl

theorem cell23_1529578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1529578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529578 prefixEnd_1529578 := by exact prefixLift 1529578
  have htrace : WordTrace (prefixWord ++ tailWord_1529578) baseStart_1529578 baseEnd_1529578 := by
    simpa [prefixWord, tailWord_1529578, baseEnd_1529578] using wordTrace_append hprefix tailTrace_1529578
  have hstable : (prefixWord ++ tailWord_1529578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529578).length < 2 ^ (prefixWord ++ tailWord_1529578).sum := by decide
  have hdescent : baseEnd_1529578 < baseStart_1529578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529624 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 7]
def baseStart_1529624 : Nat := 118140960795 + 1529624 * 2 ^ 59
def prefixEnd_1529624 : Nat := 4983230072969 + 3 ^ 40 * 1529624 * 2
def baseEnd_1529624 : Nat := 87270259183669841418377

theorem tailTrace_1529624 : CollatzResearch.WordTrace tailWord_1529624 prefixEnd_1529624 87270259183669841418377 := by
  unfold tailWord_1529624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894985305220480913005963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37193313740293974550674617 27894985305220480913005963)
  ·
    refine ⟨41842477957830721369508945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27894985305220480913005963 41842477957830721369508945)
    ·
      refine ⟨31381858468373041027131709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41842477957830721369508945 31381858468373041027131709)
      ·
        refine ⟨11768196925639890385174391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31381858468373041027131709 11768196925639890385174391)
        ·
          refine ⟨17652295388459835577761587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768196925639890385174391 17652295388459835577761587)
          ·
            refine ⟨26478443082689753366642381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652295388459835577761587 26478443082689753366642381)
            ·
              refine ⟨9929416156008657512490893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26478443082689753366642381 9929416156008657512490893)
              ·
                refine ⟨3723531058503246567184085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929416156008657512490893 3723531058503246567184085)
                ·
                  refine ⟨87270259183669841418377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3723531058503246567184085 87270259183669841418377)
                  ·
                    rfl

theorem cell23_1529624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_1529624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529624 prefixEnd_1529624 := by exact prefixLift 1529624
  have htrace : WordTrace (prefixWord ++ tailWord_1529624) baseStart_1529624 baseEnd_1529624 := by
    simpa [prefixWord, tailWord_1529624, baseEnd_1529624] using wordTrace_append hprefix tailTrace_1529624
  have hstable : (prefixWord ++ tailWord_1529624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529624).length < 2 ^ (prefixWord ++ tailWord_1529624).sum := by decide
  have hdescent : baseEnd_1529624 < baseStart_1529624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529658 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_1529658 : Nat := 118140960795 + 1529658 * 2 ^ 59
def prefixEnd_1529658 : Nat := 4983230072969 + 3 ^ 40 * 1529658 * 2
def baseEnd_1529658 : Nat := 87272198999475715526693

theorem tailTrace_1529658 : CollatzResearch.WordTrace tailWord_1529658 prefixEnd_1529658 87272198999475715526693 := by
  unfold tailWord_1529658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947802673079446408187407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37194140461545190421833085 13947802673079446408187407)
  ·
    refine ⟨20921704009619169612281111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13947802673079446408187407 20921704009619169612281111)
    ·
      refine ⟨31382556014428754418421667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20921704009619169612281111 31382556014428754418421667)
      ·
        refine ⟨47073834021643131627632501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31382556014428754418421667 47073834021643131627632501)
        ·
          refine ⟨4413171939529043590090547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47073834021643131627632501 4413171939529043590090547)
          ·
            refine ⟨6619757909293565385135821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413171939529043590090547 6619757909293565385135821)
            ·
              refine ⟨2482409215985087019425933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6619757909293565385135821 2482409215985087019425933)
              ·
                refine ⟨930903455994407632284725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482409215985087019425933 930903455994407632284725)
                ·
                  refine ⟨87272198999475715526693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930903455994407632284725 87272198999475715526693)
                  ·
                    rfl

theorem cell23_1529658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_1529658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529658 prefixEnd_1529658 := by exact prefixLift 1529658
  have htrace : WordTrace (prefixWord ++ tailWord_1529658) baseStart_1529658 baseEnd_1529658 := by
    simpa [prefixWord, tailWord_1529658, baseEnd_1529658] using wordTrace_append hprefix tailTrace_1529658
  have hstable : (prefixWord ++ tailWord_1529658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529658).length < 2 ^ (prefixWord ++ tailWord_1529658).sum := by decide
  have hdescent : baseEnd_1529658 < baseStart_1529658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529681 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_1529681 : Nat := 118140960795 + 1529681 * 2 ^ 59
def prefixEnd_1529681 : Nat := 4983230072969 + 3 ^ 40 * 1529681 * 2
def baseEnd_1529681 : Nat := 785461601050334849752631

theorem tailTrace_1529681 : CollatzResearch.WordTrace tailWord_1529681 prefixEnd_1529681 785461601050334849752631 := by
  unfold tailWord_1529681
  simp only [CollatzResearch.WordTrace]
  refine ⟨55792049571234460560836897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37194699714156307040557931 55792049571234460560836897)
  ·
    refine ⟨41844037178425845420627673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55792049571234460560836897 41844037178425845420627673)
    ·
      refine ⟨31383027883819384065470755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41844037178425845420627673 31383027883819384065470755)
      ·
        refine ⟨47074541825729076098206133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31383027883819384065470755 47074541825729076098206133)
        ·
          refine ⟨4413238296162100884206825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47074541825729076098206133 4413238296162100884206825)
          ·
            refine ⟨3309928722121575663155119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4413238296162100884206825 3309928722121575663155119)
            ·
              refine ⟨4964893083182363494732679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309928722121575663155119 4964893083182363494732679)
              ·
                refine ⟨7447339624773545242099019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964893083182363494732679 7447339624773545242099019)
                ·
                  refine ⟨11171009437160317863148529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7447339624773545242099019 11171009437160317863148529)
                  ·
                    refine ⟨8378257077870238397361397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11171009437160317863148529 8378257077870238397361397)
                    ·
                      refine ⟨785461601050334849752631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8378257077870238397361397 785461601050334849752631)
                      ·
                        rfl

theorem cell23_1529681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_1529681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529681 prefixEnd_1529681 := by exact prefixLift 1529681
  have htrace : WordTrace (prefixWord ++ tailWord_1529681) baseStart_1529681 baseEnd_1529681 := by
    simpa [prefixWord, tailWord_1529681, baseEnd_1529681] using wordTrace_append hprefix tailTrace_1529681
  have hstable : (prefixWord ++ tailWord_1529681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529681).length < 2 ^ (prefixWord ++ tailWord_1529681).sum := by decide
  have hdescent : baseEnd_1529681 < baseStart_1529681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529701 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1529701 : Nat := 118140960795 + 1529701 * 2 ^ 59
def prefixEnd_1529701 : Nat := 4983230072969 + 3 ^ 40 * 1529701 * 2
def baseEnd_1529701 : Nat := 261823956887808257167513

theorem tailTrace_1529701 : CollatzResearch.WordTrace tailWord_1529701 prefixEnd_1529701 261823956887808257167513 := by
  unfold tailWord_1529701
  simp only [CollatzResearch.WordTrace]
  refine ⟨55792779031162003976564957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37195186020774669317709971 55792779031162003976564957)
  ·
    refine ⟨20922292136685751491211859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55792779031162003976564957 20922292136685751491211859)
    ·
      refine ⟨31383438205028627236817789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20922292136685751491211859 31383438205028627236817789)
      ·
        refine ⟨11768789326885735213806671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31383438205028627236817789 11768789326885735213806671)
        ·
          refine ⟨17653183990328602820710007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768789326885735213806671 17653183990328602820710007)
          ·
            refine ⟨26479775985492904231065011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17653183990328602820710007 26479775985492904231065011)
            ·
              refine ⟨39719663978239356346597517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26479775985492904231065011 39719663978239356346597517)
              ·
                refine ⟨14894873991839758629974069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39719663978239356346597517 14894873991839758629974069)
                ·
                  refine ⟨1396394436734977371560069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14894873991839758629974069 1396394436734977371560069)
                  ·
                    refine ⟨261823956887808257167513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396394436734977371560069 261823956887808257167513)
                    ·
                      rfl

theorem cell23_1529701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1529701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529701 prefixEnd_1529701 := by exact prefixLift 1529701
  have htrace : WordTrace (prefixWord ++ tailWord_1529701) baseStart_1529701 baseEnd_1529701 := by
    simpa [prefixWord, tailWord_1529701, baseEnd_1529701] using wordTrace_append hprefix tailTrace_1529701
  have hstable : (prefixWord ++ tailWord_1529701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529701).length < 2 ^ (prefixWord ++ tailWord_1529701).sum := by decide
  have hdescent : baseEnd_1529701 < baseStart_1529701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529708 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1529708 : Nat := 118140960795 + 1529708 * 2 ^ 59
def prefixEnd_1529708 : Nat := 4983230072969 + 3 ^ 40 * 1529708 * 2
def baseEnd_1529708 : Nat := 785475465028006244115007

theorem tailTrace_1529708 : CollatzResearch.WordTrace tailWord_1529708 prefixEnd_1529708 785475465028006244115007 := by
  unfold tailWord_1529708
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896517171068322086034889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37195356228091096114713185 27896517171068322086034889)
  ·
    refine ⟨20922387878301241564526167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27896517171068322086034889 20922387878301241564526167)
    ·
      refine ⟨31383581817451862346789251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20922387878301241564526167 31383581817451862346789251)
      ·
        refine ⟨47075372726177793520183877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31383581817451862346789251 47075372726177793520183877)
        ·
          refine ⟨8826632386158336285034477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47075372726177793520183877 8826632386158336285034477)
          ·
            refine ⟨3309987144809376106887929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8826632386158336285034477 3309987144809376106887929)
            ·
              refine ⟨2482490358607032080165947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309987144809376106887929 2482490358607032080165947)
              ·
                refine ⟨3723735537910548120248921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482490358607032080165947 3723735537910548120248921)
                ·
                  refine ⟨2792801653432911090186691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723735537910548120248921 2792801653432911090186691)
                  ·
                    refine ⟨4189202480149366635280037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792801653432911090186691 4189202480149366635280037)
                    ·
                      refine ⟨785475465028006244115007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4189202480149366635280037 785475465028006244115007)
                      ·
                        rfl

theorem cell23_1529708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1529708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529708 prefixEnd_1529708 := by exact prefixLift 1529708
  have htrace : WordTrace (prefixWord ++ tailWord_1529708) baseStart_1529708 baseEnd_1529708 := by
    simpa [prefixWord, tailWord_1529708, baseEnd_1529708] using wordTrace_append hprefix tailTrace_1529708
  have hstable : (prefixWord ++ tailWord_1529708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529708).length < 2 ^ (prefixWord ++ tailWord_1529708).sum := by decide
  have hdescent : baseEnd_1529708 < baseStart_1529708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529731 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 6]
def baseStart_1529731 : Nat := 118140960795 + 1529731 * 2 ^ 59
def prefixEnd_1529731 : Nat := 4983230072969 + 3 ^ 40 * 1529731 * 2
def baseEnd_1529731 : Nat := 87276363898117739347489

theorem tailTrace_1529731 : CollatzResearch.WordTrace tailWord_1529731 prefixEnd_1529731 87276363898117739347489 := by
  unfold tailWord_1529731
  simp only [CollatzResearch.WordTrace]
  refine ⟨55793873221053319100157047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37195915480702212733438031 55793873221053319100157047)
  ·
    refine ⟨83690809831579978650235571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55793873221053319100157047 83690809831579978650235571)
    ·
      refine ⟨125536214747369967975353357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83690809831579978650235571 125536214747369967975353357)
      ·
        refine ⟨47076080530263737990757509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125536214747369967975353357 47076080530263737990757509)
        ·
          refine ⟨8826765099424450873267033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47076080530263737990757509 8826765099424450873267033)
          ·
            refine ⟨6620073824568338154950275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8826765099424450873267033 6620073824568338154950275)
            ·
              refine ⟨9930110736852507232425413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620073824568338154950275 9930110736852507232425413)
              ·
                refine ⟨1861895763159845106079765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9930110736852507232425413 1861895763159845106079765)
                ·
                  refine ⟨87276363898117739347489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861895763159845106079765 87276363898117739347489)
                  ·
                    rfl

theorem cell23_1529731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 6].length) (baseStart_1529731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529731 prefixEnd_1529731 := by exact prefixLift 1529731
  have htrace : WordTrace (prefixWord ++ tailWord_1529731) baseStart_1529731 baseEnd_1529731 := by
    simpa [prefixWord, tailWord_1529731, baseEnd_1529731] using wordTrace_append hprefix tailTrace_1529731
  have hstable : (prefixWord ++ tailWord_1529731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529731).length < 2 ^ (prefixWord ++ tailWord_1529731).sum := by decide
  have hdescent : baseEnd_1529731 < baseStart_1529731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529742 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1529742 : Nat := 118140960795 + 1529742 * 2 ^ 59
def prefixEnd_1529742 : Nat := 4983230072969 + 3 ^ 40 * 1529742 * 2
def baseEnd_1529742 : Nat := 785492923370259111089851

theorem tailTrace_1529742 : CollatzResearch.WordTrace tailWord_1529742 prefixEnd_1529742 785492923370259111089851 := by
  unfold tailWord_1529742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974284303001683497350935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37196182949342311985871653 6974284303001683497350935)
  ·
    refine ⟨10461426454502525246026403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974284303001683497350935 10461426454502525246026403)
    ·
      refine ⟨15692139681753787869039605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10461426454502525246026403 15692139681753787869039605)
      ·
        refine ⟨1471138095164417612722463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15692139681753787869039605 1471138095164417612722463)
        ·
          refine ⟨2206707142746626419083695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471138095164417612722463 2206707142746626419083695)
          ·
            refine ⟨3310060714119939628625543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206707142746626419083695 3310060714119939628625543)
            ·
              refine ⟨4965091071179909442938315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310060714119939628625543 4965091071179909442938315)
              ·
                refine ⟨7447636606769864164407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965091071179909442938315 7447636606769864164407473)
                ·
                  refine ⟨5585727455077398123305605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7447636606769864164407473 5585727455077398123305605)
                  ·
                    refine ⟨1047323897827012148119801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5585727455077398123305605 1047323897827012148119801)
                    ·
                      refine ⟨785492923370259111089851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047323897827012148119801 785492923370259111089851)
                      ·
                        rfl

theorem cell23_1529742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1529742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529742 prefixEnd_1529742 := by exact prefixLift 1529742
  have htrace : WordTrace (prefixWord ++ tailWord_1529742) baseStart_1529742 baseEnd_1529742 := by
    simpa [prefixWord, tailWord_1529742, baseEnd_1529742] using wordTrace_append hprefix tailTrace_1529742
  have hstable : (prefixWord ++ tailWord_1529742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529742).length < 2 ^ (prefixWord ++ tailWord_1529742).sum := by decide
  have hdescent : baseEnd_1529742 < baseStart_1529742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529744 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_1529744 : Nat := 118140960795 + 1529744 * 2 ^ 59
def prefixEnd_1529744 : Nat := 4983230072969 + 3 ^ 40 * 1529744 * 2
def baseEnd_1529744 : Nat := 261831316777189367754947

theorem tailTrace_1529744 : CollatzResearch.WordTrace tailWord_1529744 prefixEnd_1529744 261831316777189367754947 := by
  unfold tailWord_1529744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897173685003111160190143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37196231580004148213586857 27897173685003111160190143)
  ·
    refine ⟨41845760527504666740285215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27897173685003111160190143 41845760527504666740285215)
    ·
      refine ⟨62768640791257000110427823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41845760527504666740285215 62768640791257000110427823)
      ·
        refine ⟨94152961186885500165641735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62768640791257000110427823 94152961186885500165641735)
        ·
          refine ⟨141229441780328250248462603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94152961186885500165641735 141229441780328250248462603)
          ·
            refine ⟨211844162670492375372693905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141229441780328250248462603 211844162670492375372693905)
            ·
              refine ⟨158883122002869281529520429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211844162670492375372693905 158883122002869281529520429)
              ·
                refine ⟨59581170751075980573570161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158883122002869281529520429 59581170751075980573570161)
                ·
                  refine ⟨44685878063306985430177621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59581170751075980573570161 44685878063306985430177621)
                  ·
                    refine ⟨261831316777189367754947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44685878063306985430177621 261831316777189367754947)
                    ·
                      rfl

theorem cell23_1529744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_1529744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529744 prefixEnd_1529744 := by exact prefixLift 1529744
  have htrace : WordTrace (prefixWord ++ tailWord_1529744) baseStart_1529744 baseEnd_1529744 := by
    simpa [prefixWord, tailWord_1529744, baseEnd_1529744] using wordTrace_append hprefix tailTrace_1529744
  have hstable : (prefixWord ++ tailWord_1529744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529744).length < 2 ^ (prefixWord ++ tailWord_1529744).sum := by decide
  have hdescent : baseEnd_1529744 < baseStart_1529744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529748 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1529748 : Nat := 118140960795 + 1529748 * 2 ^ 59
def prefixEnd_1529748 : Nat := 4983230072969 + 3 ^ 40 * 1529748 * 2
def baseEnd_1529748 : Nat := 87277333806020676401647

theorem tailTrace_1529748 : CollatzResearch.WordTrace tailWord_1529748 prefixEnd_1529748 87277333806020676401647 := by
  unfold tailWord_1529748
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897246630995865501762949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37196328841327820669017265 27897246630995865501762949)
  ·
    refine ⟨5230733743311724781580553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27897246630995865501762949 5230733743311724781580553)
    ·
      refine ⟨3923050307483793586185415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230733743311724781580553 3923050307483793586185415)
      ·
        refine ⟨5884575461225690379278123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923050307483793586185415 5884575461225690379278123)
        ·
          refine ⟨8826863191838535568917185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884575461225690379278123 8826863191838535568917185)
          ·
            refine ⟨6620147393878901676687889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8826863191838535568917185 6620147393878901676687889)
            ·
              refine ⟨4965110545409176257515917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6620147393878901676687889 4965110545409176257515917)
              ·
                refine ⟨1861916454528441096568469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4965110545409176257515917 1861916454528441096568469)
                ·
                  refine ⟨87277333806020676401647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861916454528441096568469 87277333806020676401647)
                  ·
                    rfl

theorem cell23_1529748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1529748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529748 prefixEnd_1529748 := by exact prefixLift 1529748
  have htrace : WordTrace (prefixWord ++ tailWord_1529748) baseStart_1529748 baseEnd_1529748 := by
    simpa [prefixWord, tailWord_1529748, baseEnd_1529748] using wordTrace_append hprefix tailTrace_1529748
  have hstable : (prefixWord ++ tailWord_1529748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529748).length < 2 ^ (prefixWord ++ tailWord_1529748).sum := by decide
  have hdescent : baseEnd_1529748 < baseStart_1529748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529762 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1529762 : Nat := 118140960795 + 1529762 * 2 ^ 59
def prefixEnd_1529762 : Nat := 4983230072969 + 3 ^ 40 * 1529762 * 2
def baseEnd_1529762 : Nat := 785503192983349032839759

theorem tailTrace_1529762 : CollatzResearch.WordTrace tailWord_1529762 prefixEnd_1529762 785503192983349032839759 := by
  unfold tailWord_1529762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13948750970985252848633885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37196669255960674263023693 13948750970985252848633885)
  ·
    refine ⟨5230781614119469818237707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13948750970985252848633885 5230781614119469818237707)
    ·
      refine ⟨7846172421179204727356561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230781614119469818237707 7846172421179204727356561)
      ·
        refine ⟨5884629315884403545517421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7846172421179204727356561 5884629315884403545517421)
        ·
          refine ⟨2206735993456651329569033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5884629315884403545517421 2206735993456651329569033)
          ·
            refine ⟨1655051995092488497176775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206735993456651329569033 1655051995092488497176775)
            ·
              refine ⟨2482577992638732745765163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655051995092488497176775 2482577992638732745765163)
              ·
                refine ⟨3723866988958099118647745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482577992638732745765163 3723866988958099118647745)
                ·
                  refine ⟨2792900241718574338985809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723866988958099118647745 2792900241718574338985809)
                  ·
                    refine ⟨2094675181288930754239357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2792900241718574338985809 2094675181288930754239357)
                    ·
                      refine ⟨785503192983349032839759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2094675181288930754239357 785503192983349032839759)
                      ·
                        rfl

theorem cell23_1529762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1529762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529762 prefixEnd_1529762 := by exact prefixLift 1529762
  have htrace : WordTrace (prefixWord ++ tailWord_1529762) baseStart_1529762 baseEnd_1529762 := by
    simpa [prefixWord, tailWord_1529762, baseEnd_1529762] using wordTrace_append hprefix tailTrace_1529762
  have hstable : (prefixWord ++ tailWord_1529762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529762).length < 2 ^ (prefixWord ++ tailWord_1529762).sum := by decide
  have hdescent : baseEnd_1529762 < baseStart_1529762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529801 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_1529801 : Nat := 118140960795 + 1529801 * 2 ^ 59
def prefixEnd_1529801 : Nat := 4983230072969 + 3 ^ 40 * 1529801 * 2
def baseEnd_1529801 : Nat := 785523218728874380252079

theorem tailTrace_1529801 : CollatzResearch.WordTrace tailWord_1529801 prefixEnd_1529801 785523218728874380252079 := by
  unfold tailWord_1529801
  simp only [CollatzResearch.WordTrace]
  refine ⟨55796426330799721055205257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37197617553866480703470171 55796426330799721055205257)
  ·
    refine ⟨41847319748099790791403943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55796426330799721055205257 41847319748099790791403943)
    ·
      refine ⟨62770979622149686187105915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41847319748099790791403943 62770979622149686187105915)
      ·
        refine ⟨94156469433224529280658873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62770979622149686187105915 94156469433224529280658873)
        ·
          refine ⟨70617352074918396960494155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94156469433224529280658873 70617352074918396960494155)
          ·
            refine ⟨105926028112377595440741233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70617352074918396960494155 105926028112377595440741233)
            ·
              refine ⟨79444521084283196580555925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105926028112377595440741233 79444521084283196580555925)
              ·
                refine ⟨3723961925825774839713559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79444521084283196580555925 3723961925825774839713559)
                ·
                  refine ⟨5585942888738662259570339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723961925825774839713559 5585942888738662259570339)
                  ·
                    refine ⟨8378914333107993389355509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5585942888738662259570339 8378914333107993389355509)
                    ·
                      refine ⟨785523218728874380252079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8378914333107993389355509 785523218728874380252079)
                      ·
                        rfl

theorem cell23_1529801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_1529801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529801 prefixEnd_1529801 := by exact prefixLift 1529801
  have htrace : WordTrace (prefixWord ++ tailWord_1529801) baseStart_1529801 baseEnd_1529801 := by
    simpa [prefixWord, tailWord_1529801, baseEnd_1529801] using wordTrace_append hprefix tailTrace_1529801
  have hstable : (prefixWord ++ tailWord_1529801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529801).length < 2 ^ (prefixWord ++ tailWord_1529801).sum := by decide
  have hdescent : baseEnd_1529801 < baseStart_1529801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529808 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_1529808 : Nat := 118140960795 + 1529808 * 2 ^ 59
def prefixEnd_1529808 : Nat := 4983230072969 + 3 ^ 40 * 1529808 * 2
def baseEnd_1529808 : Nat := 261842271031151950954849

theorem tailTrace_1529808 : CollatzResearch.WordTrace tailWord_1529808 prefixEnd_1529808 261842271031151950954849 := by
  unfold tailWord_1529808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898340820887180625355039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37197787761182907500473385 27898340820887180625355039)
  ·
    refine ⟨41847511231330770938032559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27898340820887180625355039 41847511231330770938032559)
    ·
      refine ⟨62771266846996156407048839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41847511231330770938032559 62771266846996156407048839)
      ·
        refine ⟨94156900270494234610573259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62771266846996156407048839 94156900270494234610573259)
        ·
          refine ⟨141235350405741351915859889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94156900270494234610573259 141235350405741351915859889)
          ·
            refine ⟨105926512804306013936894917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141235350405741351915859889 105926512804306013936894917)
            ·
              refine ⟨19861221150807377613167797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105926512804306013936894917 19861221150807377613167797)
              ·
                refine ⟨1861989482888191651234481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19861221150807377613167797 1861989482888191651234481)
                ·
                  refine ⟨1396492112166143738425861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861989482888191651234481 1396492112166143738425861)
                  ·
                    refine ⟨261842271031151950954849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396492112166143738425861 261842271031151950954849)
                    ·
                      rfl

theorem cell23_1529808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_1529808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529808 prefixEnd_1529808 := by exact prefixLift 1529808
  have htrace : WordTrace (prefixWord ++ tailWord_1529808) baseStart_1529808 baseEnd_1529808 := by
    simpa [prefixWord, tailWord_1529808, baseEnd_1529808] using wordTrace_append hprefix tailTrace_1529808
  have hstable : (prefixWord ++ tailWord_1529808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529808).length < 2 ^ (prefixWord ++ tailWord_1529808).sum := by decide
  have hdescent : baseEnd_1529808 < baseStart_1529808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529815 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_1529815 : Nat := 118140960795 + 1529815 * 2 ^ 59
def prefixEnd_1529815 : Nat := 4983230072969 + 3 ^ 40 * 1529815 * 2
def baseEnd_1529815 : Nat := 785530407458037325477015

theorem tailTrace_1529815 : CollatzResearch.WordTrace tailWord_1529815 prefixEnd_1529815 785530407458037325477015 := by
  unfold tailWord_1529815
  simp only [CollatzResearch.WordTrace]
  refine ⟨55796936952749001446214899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37197957968499334297476599 55796936952749001446214899)
  ·
    refine ⟨83695405429123502169322349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55796936952749001446214899 83695405429123502169322349)
    ·
      refine ⟨31385777035921313313495881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83695405429123502169322349 31385777035921313313495881)
      ·
        refine ⟨23539332776940984985121911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31385777035921313313495881 23539332776940984985121911)
        ·
          refine ⟨35308999165411477477682867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23539332776940984985121911 35308999165411477477682867)
          ·
            refine ⟨52963498748117216216524301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35308999165411477477682867 52963498748117216216524301)
            ·
              refine ⟨19861312030543956081196613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52963498748117216216524301 19861312030543956081196613)
              ·
                refine ⟨3723996005726991765224365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19861312030543956081196613 3723996005726991765224365)
                ·
                  refine ⟨1396498502147621911959137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3723996005726991765224365 1396498502147621911959137)
                  ·
                    refine ⟨1047373876610716433969353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396498502147621911959137 1047373876610716433969353)
                    ·
                      refine ⟨785530407458037325477015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047373876610716433969353 785530407458037325477015)
                      ·
                        rfl

theorem cell23_1529815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_1529815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529815 prefixEnd_1529815 := by exact prefixLift 1529815
  have htrace : WordTrace (prefixWord ++ tailWord_1529815) baseStart_1529815 baseEnd_1529815 := by
    simpa [prefixWord, tailWord_1529815, baseEnd_1529815] using wordTrace_append hprefix tailTrace_1529815
  have hstable : (prefixWord ++ tailWord_1529815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529815).length < 2 ^ (prefixWord ++ tailWord_1529815).sum := by decide
  have hdescent : baseEnd_1529815 < baseStart_1529815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529838 : List Nat := [4, 1, 2, 1, 3, 3, 9]
def baseStart_1529838 : Nat := 118140960795 + 1529838 * 2 ^ 59
def prefixEnd_1529838 : Nat := 4983230072969 + 3 ^ 40 * 1529838 * 2
def baseEnd_1529838 : Nat := 9698052068062848586289

theorem tailTrace_1529838 : CollatzResearch.WordTrace tailWord_1529838 prefixEnd_1529838 9698052068062848586289 := by
  unfold tailWord_1529838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974721978958209546787771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37198517221110450916201445 6974721978958209546787771)
  ·
    refine ⟨10462082968437314320181657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974721978958209546787771 10462082968437314320181657)
    ·
      refine ⟨7846562226327985740136243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10462082968437314320181657 7846562226327985740136243)
      ·
        refine ⟨11769843339491978610204365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7846562226327985740136243 11769843339491978610204365)
        ·
          refine ⟨4413691252309491978826637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11769843339491978610204365 4413691252309491978826637)
          ·
            refine ⟨1655134219616059492059989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4413691252309491978826637 1655134219616059492059989)
            ·
              refine ⟨9698052068062848586289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1655134219616059492059989 9698052068062848586289)
              ·
                rfl

theorem cell23_1529838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 9].length) (baseStart_1529838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529838 prefixEnd_1529838 := by exact prefixLift 1529838
  have htrace : WordTrace (prefixWord ++ tailWord_1529838) baseStart_1529838 baseEnd_1529838 := by
    simpa [prefixWord, tailWord_1529838, baseEnd_1529838] using wordTrace_append hprefix tailTrace_1529838
  have hstable : (prefixWord ++ tailWord_1529838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529838).length < 2 ^ (prefixWord ++ tailWord_1529838).sum := by decide
  have hdescent : baseEnd_1529838 < baseStart_1529838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529881 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_1529881 : Nat := 118140960795 + 1529881 * 2 ^ 59
def prefixEnd_1529881 : Nat := 4983230072969 + 3 ^ 40 * 1529881 * 2
def baseEnd_1529881 : Nat := 261854765727078022417237

theorem tailTrace_1529881 : CollatzResearch.WordTrace tailWord_1529881 prefixEnd_1529881 261854765727078022417237 := by
  unfold tailWord_1529881
  simp only [CollatzResearch.WordTrace]
  refine ⟨55799344170509894718117497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37199562780339929812078331 55799344170509894718117497)
  ·
    refine ⟨41849508127882421038588123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55799344170509894718117497 41849508127882421038588123)
    ·
      refine ⟨62774262191823631557882185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41849508127882421038588123 62774262191823631557882185)
      ·
        refine ⟨47080696643867723668411639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62774262191823631557882185 47080696643867723668411639)
        ·
          refine ⟨70621044965801585502617459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47080696643867723668411639 70621044965801585502617459)
          ·
            refine ⟨105931567448702378253926189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70621044965801585502617459 105931567448702378253926189)
            ·
              refine ⟨39724337793263391845222321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105931567448702378253926189 39724337793263391845222321)
              ·
                refine ⟨29793253344947543883916741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39724337793263391845222321 29793253344947543883916741)
                ·
                  refine ⟨5586235002177664478234389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29793253344947543883916741 5586235002177664478234389)
                  ·
                    refine ⟨261854765727078022417237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5586235002177664478234389 261854765727078022417237)
                    ·
                      rfl

theorem cell23_1529881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_1529881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529881 prefixEnd_1529881 := by exact prefixLift 1529881
  have htrace : WordTrace (prefixWord ++ tailWord_1529881) baseStart_1529881 baseEnd_1529881 := by
    simpa [prefixWord, tailWord_1529881, baseEnd_1529881] using wordTrace_append hprefix tailTrace_1529881
  have hstable : (prefixWord ++ tailWord_1529881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529881).length < 2 ^ (prefixWord ++ tailWord_1529881).sum := by decide
  have hdescent : baseEnd_1529881 < baseStart_1529881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529931 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_1529931 : Nat := 118140960795 + 1529931 * 2 ^ 59
def prefixEnd_1529931 : Nat := 4983230072969 + 3 ^ 40 * 1529931 * 2
def baseEnd_1529931 : Nat := 785589971213958871626481

theorem tailTrace_1529931 : CollatzResearch.WordTrace tailWord_1529931 prefixEnd_1529931 785589971213958871626481 := by
  unfold tailWord_1529931
  simp only [CollatzResearch.WordTrace]
  refine ⟨55801167820328753257437647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37200778546885835504958431 55801167820328753257437647)
  ·
    refine ⟨83701751730493129886156471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55801167820328753257437647 83701751730493129886156471)
    ·
      refine ⟨125552627595739694829234707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83701751730493129886156471 125552627595739694829234707)
      ·
        refine ⟨188328941393609542243852061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125552627595739694829234707 188328941393609542243852061)
        ·
          refine ⟨70623353022603578341444523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188328941393609542243852061 70623353022603578341444523)
          ·
            refine ⟨105935029533905367512166785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70623353022603578341444523 105935029533905367512166785)
            ·
              refine ⟨79451272150429025634125089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105935029533905367512166785 79451272150429025634125089)
              ·
                refine ⟨59588454112821769225593817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79451272150429025634125089 59588454112821769225593817)
                ·
                  refine ⟨44691340584616326919195363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59588454112821769225593817 44691340584616326919195363)
                  ·
                    refine ⟨67037010876924490378793045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44691340584616326919195363 67037010876924490378793045)
                    ·
                      refine ⟨785589971213958871626481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 67037010876924490378793045 785589971213958871626481)
                      ·
                        rfl

theorem cell23_1529931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_1529931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529931 prefixEnd_1529931 := by exact prefixLift 1529931
  have htrace : WordTrace (prefixWord ++ tailWord_1529931) baseStart_1529931 baseEnd_1529931 := by
    simpa [prefixWord, tailWord_1529931, baseEnd_1529931] using wordTrace_append hprefix tailTrace_1529931
  have hstable : (prefixWord ++ tailWord_1529931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529931).length < 2 ^ (prefixWord ++ tailWord_1529931).sum := by decide
  have hdescent : baseEnd_1529931 < baseStart_1529931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529945 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 5]
def baseStart_1529945 : Nat := 118140960795 + 1529945 * 2 ^ 59
def prefixEnd_1529945 : Nat := 4983230072969 + 3 ^ 40 * 1529945 * 2
def baseEnd_1529945 : Nat := 87288573327013535205713

theorem tailTrace_1529945 : CollatzResearch.WordTrace tailWord_1529945 prefixEnd_1529945 87288573327013535205713 := by
  unfold tailWord_1529945
  simp only [CollatzResearch.WordTrace]
  refine ⟨55801678442278033648447289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37201118961518689098964859 55801678442278033648447289)
  ·
    refine ⟨41851258831708525236335467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55801678442278033648447289 41851258831708525236335467)
    ·
      refine ⟨62776888247562787854503201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41851258831708525236335467 62776888247562787854503201)
      ·
        refine ⟨47082666185672090890877401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62776888247562787854503201 47082666185672090890877401)
        ·
          refine ⟨35311999639254068168158051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47082666185672090890877401 35311999639254068168158051)
          ·
            refine ⟨52967999458881102252237077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35311999639254068168158051 52967999458881102252237077)
            ·
              refine ⟨2482874974635051668073613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52967999458881102252237077 2482874974635051668073613)
              ·
                refine ⟨931078115488144375527605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482874974635051668073613 931078115488144375527605)
                ·
                  refine ⟨87288573327013535205713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931078115488144375527605 87288573327013535205713)
                  ·
                    rfl

theorem cell23_1529945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 5].length) (baseStart_1529945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529945 prefixEnd_1529945 := by exact prefixLift 1529945
  have htrace : WordTrace (prefixWord ++ tailWord_1529945) baseStart_1529945 baseEnd_1529945 := by
    simpa [prefixWord, tailWord_1529945, baseEnd_1529945] using wordTrace_append hprefix tailTrace_1529945
  have hstable : (prefixWord ++ tailWord_1529945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529945).length < 2 ^ (prefixWord ++ tailWord_1529945).sum := by decide
  have hdescent : baseEnd_1529945 < baseStart_1529945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529950 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1529950 : Nat := 118140960795 + 1529950 * 2 ^ 59
def prefixEnd_1529950 : Nat := 4983230072969 + 3 ^ 40 * 1529950 * 2
def baseEnd_1529950 : Nat := 785599727346394297288895

theorem tailTrace_1529950 : CollatzResearch.WordTrace tailWord_1529950 prefixEnd_1529950 785599727346394297288895 := by
  unfold tailWord_1529950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975232600907489937797413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37201240538173279668252869 6975232600907489937797413)
  ·
    refine ⟨1307856112670154363337015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6975232600907489937797413 1307856112670154363337015)
    ·
      refine ⟨1961784169005231545005523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307856112670154363337015 1961784169005231545005523)
      ·
        refine ⟨2942676253507847317508285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961784169005231545005523 2942676253507847317508285)
        ·
          refine ⟨1103503595065442744065607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2942676253507847317508285 1103503595065442744065607)
          ·
            refine ⟨1655255392598164116098411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103503595065442744065607 1655255392598164116098411)
            ·
              refine ⟨2482883088897246174147617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655255392598164116098411 2482883088897246174147617)
              ·
                refine ⟨1862162316672934630610713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482883088897246174147617 1862162316672934630610713)
                ·
                  refine ⟨1396621737504700972958035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862162316672934630610713 1396621737504700972958035)
                  ·
                    refine ⟨2094932606257051459437053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1396621737504700972958035 2094932606257051459437053)
                    ·
                      refine ⟨785599727346394297288895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2094932606257051459437053 785599727346394297288895)
                      ·
                        rfl

theorem cell23_1529950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1529950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529950 prefixEnd_1529950 := by exact prefixLift 1529950
  have htrace : WordTrace (prefixWord ++ tailWord_1529950) baseStart_1529950 baseEnd_1529950 := by
    simpa [prefixWord, tailWord_1529950, baseEnd_1529950] using wordTrace_append hprefix tailTrace_1529950
  have hstable : (prefixWord ++ tailWord_1529950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529950).length < 2 ^ (prefixWord ++ tailWord_1529950).sum := by decide
  have hdescent : baseEnd_1529950 < baseStart_1529950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529988 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1529988 : Nat := 118140960795 + 1529988 * 2 ^ 59
def prefixEnd_1529988 : Nat := 4983230072969 + 3 ^ 40 * 1529988 * 2
def baseEnd_1529988 : Nat := 261873079870421716204573

theorem tailTrace_1529988 : CollatzResearch.WordTrace tailWord_1529988 prefixEnd_1529988 261873079870421716204573 := by
  unfold tailWord_1529988
  simp only [CollatzResearch.WordTrace]
  refine ⟨27901623390561125996131309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37202164520748167994841745 27901623390561125996131309)
  ·
    refine ⟨10463108771460422248549241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27901623390561125996131309 10463108771460422248549241)
    ·
      refine ⟨7847331578595316686411931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463108771460422248549241 7847331578595316686411931)
      ·
        refine ⟨11770997367892975029617897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847331578595316686411931 11770997367892975029617897)
        ·
          refine ⟨8828248025919731272213423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11770997367892975029617897 8828248025919731272213423)
          ·
            refine ⟨13242372038879596908320135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828248025919731272213423 13242372038879596908320135)
            ·
              refine ⟨19863558058319395362480203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13242372038879596908320135 19863558058319395362480203)
              ·
                refine ⟨29795337087479093043720305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19863558058319395362480203 29795337087479093043720305)
                ·
                  refine ⟨22346502815609319782790229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29795337087479093043720305 22346502815609319782790229)
                  ·
                    refine ⟨261873079870421716204573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22346502815609319782790229 261873079870421716204573)
                    ·
                      rfl

theorem cell23_1529988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1529988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1529988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1529988 prefixEnd_1529988 := by exact prefixLift 1529988
  have htrace : WordTrace (prefixWord ++ tailWord_1529988) baseStart_1529988 baseEnd_1529988 := by
    simpa [prefixWord, tailWord_1529988, baseEnd_1529988] using wordTrace_append hprefix tailTrace_1529988
  have hstable : (prefixWord ++ tailWord_1529988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529988).length < 2 ^ (prefixWord ++ tailWord_1529988).sum := by decide
  have hdescent : baseEnd_1529988 < baseStart_1529988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530065 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_1530065 : Nat := 118140960795 + 1530065 * 2 ^ 59
def prefixEnd_1530065 : Nat := 4983230072969 + 3 ^ 40 * 1530065 * 2
def baseEnd_1530065 : Nat := 261886259207220449116955

theorem tailTrace_1530065 : CollatzResearch.WordTrace tailWord_1530065 prefixEnd_1530065 261886259207220449116955 := by
  unfold tailWord_1530065
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806055201843294142815649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37204036801228862761877099 55806055201843294142815649)
  ·
    refine ⟨41854541401382470607111737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55806055201843294142815649 41854541401382470607111737)
    ·
      refine ⟨31390906051036852955333803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41854541401382470607111737 31390906051036852955333803)
      ·
        refine ⟨47086359076555279433000705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31390906051036852955333803 47086359076555279433000705)
        ·
          refine ⟨35314769307416459574750529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47086359076555279433000705 35314769307416459574750529)
          ·
            refine ⟨26486076980562344681062897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35314769307416459574750529 26486076980562344681062897)
            ·
              refine ⟨19864557735421758510797173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26486076980562344681062897 19864557735421758510797173)
              ·
                refine ⟨1862302287695789860387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19864557735421758510797173 1862302287695789860387235)
                ·
                  refine ⟨2793453431543684790580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862302287695789860387235 2793453431543684790580853)
                  ·
                    refine ⟨261886259207220449116955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2793453431543684790580853 261886259207220449116955)
                    ·
                      rfl

theorem cell23_1530065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_1530065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530065 prefixEnd_1530065 := by exact prefixLift 1530065
  have htrace : WordTrace (prefixWord ++ tailWord_1530065) baseStart_1530065 baseEnd_1530065 := by
    simpa [prefixWord, tailWord_1530065, baseEnd_1530065] using wordTrace_append hprefix tailTrace_1530065
  have hstable : (prefixWord ++ tailWord_1530065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530065).length < 2 ^ (prefixWord ++ tailWord_1530065).sum := by decide
  have hdescent : baseEnd_1530065 < baseStart_1530065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530095 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 6]
def baseStart_1530095 : Nat := 118140960795 + 1530095 * 2 ^ 59
def prefixEnd_1530095 : Nat := 4983230072969 + 3 ^ 40 * 1530095 * 2
def baseEnd_1530095 : Nat := 261891394013765409991909

theorem tailTrace_1530095 : CollatzResearch.WordTrace tailWord_1530095 prefixEnd_1530095 261891394013765409991909 := by
  unfold tailWord_1530095
  simp only [CollatzResearch.WordTrace]
  refine ⟨55807149391734609266407739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37204766261156406177605159 55807149391734609266407739)
  ·
    refine ⟨83710724087601913899611609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55807149391734609266407739 83710724087601913899611609)
    ·
      refine ⟨62783043065701435424708707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83710724087601913899611609 62783043065701435424708707)
      ·
        refine ⟨94174564598552153137063061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62783043065701435424708707 94174564598552153137063061)
        ·
          refine ⟨4414432715557132178299831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94174564598552153137063061 4414432715557132178299831)
          ·
            refine ⟨6621649073335698267449747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414432715557132178299831 6621649073335698267449747)
            ·
              refine ⟨9932473610003547401174621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621649073335698267449747 9932473610003547401174621)
              ·
                refine ⟨3724677603751330275440483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932473610003547401174621 3724677603751330275440483)
                ·
                  refine ⟨5587016405626995413160725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724677603751330275440483 5587016405626995413160725)
                  ·
                    refine ⟨261891394013765409991909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5587016405626995413160725 261891394013765409991909)
                    ·
                      rfl

theorem cell23_1530095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_1530095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530095 prefixEnd_1530095 := by exact prefixLift 1530095
  have htrace : WordTrace (prefixWord ++ tailWord_1530095) baseStart_1530095 baseEnd_1530095 := by
    simpa [prefixWord, tailWord_1530095, baseEnd_1530095] using wordTrace_append hprefix tailTrace_1530095
  have hstable : (prefixWord ++ tailWord_1530095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530095).length < 2 ^ (prefixWord ++ tailWord_1530095).sum := by decide
  have hdescent : baseEnd_1530095 < baseStart_1530095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530102 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1530102 : Nat := 118140960795 + 1530102 * 2 ^ 59
def prefixEnd_1530102 : Nat := 4983230072969 + 3 ^ 40 * 1530102 * 2
def baseEnd_1530102 : Nat := 785677776405877702588195

theorem tailTrace_1530102 : CollatzResearch.WordTrace tailWord_1530102 prefixEnd_1530102 785677776405877702588195 := by
  unfold tailWord_1530102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487962793919328091369535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37204936468472832974608373 3487962793919328091369535)
  ·
    refine ⟨5231944190878992137054303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487962793919328091369535 5231944190878992137054303)
    ·
      refine ⟨7847916286318488205581455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231944190878992137054303 7847916286318488205581455)
      ·
        refine ⟨11771874429477732308372183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847916286318488205581455 11771874429477732308372183)
        ·
          refine ⟨17657811644216598462558275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771874429477732308372183 17657811644216598462558275)
          ·
            refine ⟨26486717466324897693837413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17657811644216598462558275 26486717466324897693837413)
            ·
              refine ⟨4966259524935918317594515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26486717466324897693837413 4966259524935918317594515)
              ·
                refine ⟨7449389287403877476391773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966259524935918317594515 7449389287403877476391773)
                ·
                  refine ⟨2793520982776454053646915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7449389287403877476391773 2793520982776454053646915)
                  ·
                    refine ⟨4190281474164681080470373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2793520982776454053646915 4190281474164681080470373)
                    ·
                      refine ⟨785677776405877702588195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4190281474164681080470373 785677776405877702588195)
                      ·
                        rfl

theorem cell23_1530102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1530102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530102 prefixEnd_1530102 := by exact prefixLift 1530102
  have htrace : WordTrace (prefixWord ++ tailWord_1530102) baseStart_1530102 baseEnd_1530102 := by
    simpa [prefixWord, tailWord_1530102, baseEnd_1530102] using wordTrace_append hprefix tailTrace_1530102
  have hstable : (prefixWord ++ tailWord_1530102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530102).length < 2 ^ (prefixWord ++ tailWord_1530102).sum := by decide
  have hdescent : baseEnd_1530102 < baseStart_1530102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530115 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1530115 : Nat := 118140960795 + 1530115 * 2 ^ 59
def prefixEnd_1530115 : Nat := 4983230072969 + 3 ^ 40 * 1530115 * 2
def baseEnd_1530115 : Nat := 785684451654386151725635

theorem tailTrace_1530115 : CollatzResearch.WordTrace tailWord_1530115 prefixEnd_1530115 785684451654386151725635 := by
  unfold tailWord_1530115
  simp only [CollatzResearch.WordTrace]
  refine ⟨55807878851662152682135799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37205252567774768454757199 55807878851662152682135799)
  ·
    refine ⟨83711818277493229023203699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55807878851662152682135799 83711818277493229023203699)
    ·
      refine ⟨125567727416239843534805549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83711818277493229023203699 125567727416239843534805549)
      ·
        refine ⟨47087897781089941325552081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125567727416239843534805549 47087897781089941325552081)
        ·
          refine ⟨35315923335817455994164061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47087897781089941325552081 35315923335817455994164061)
          ·
            refine ⟨13243471250931545997811523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35315923335817455994164061 13243471250931545997811523)
            ·
              refine ⟨19865206876397318996717285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243471250931545997811523 19865206876397318996717285)
              ·
                refine ⟨3724726289324497311884491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19865206876397318996717285 3724726289324497311884491)
                ·
                  refine ⟨5587089433986745967826737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724726289324497311884491 5587089433986745967826737)
                  ·
                    refine ⟨4190317075490059475870053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587089433986745967826737 4190317075490059475870053)
                    ·
                      refine ⟨785684451654386151725635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4190317075490059475870053 785684451654386151725635)
                      ·
                        rfl

theorem cell23_1530115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1530115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530115 prefixEnd_1530115 := by exact prefixLift 1530115
  have htrace : WordTrace (prefixWord ++ tailWord_1530115) baseStart_1530115 baseEnd_1530115 := by
    simpa [prefixWord, tailWord_1530115, baseEnd_1530115] using wordTrace_append hprefix tailTrace_1530115
  have hstable : (prefixWord ++ tailWord_1530115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530115).length < 2 ^ (prefixWord ++ tailWord_1530115).sum := by decide
  have hdescent : baseEnd_1530115 < baseStart_1530115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530116 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1530116 : Nat := 118140960795 + 1530116 * 2 ^ 59
def prefixEnd_1530116 : Nat := 4983230072969 + 3 ^ 40 * 1530116 * 2
def baseEnd_1530116 : Nat := 261894988378346882604377

theorem tailTrace_1530116 : CollatzResearch.WordTrace tailWord_1530116 prefixEnd_1530116 261894988378346882604377 := by
  unfold tailWord_1530116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27903957662329264926461101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37205276883105686568614801 27903957662329264926461101)
  ·
    refine ⟨10463984123373474347422913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27903957662329264926461101 10463984123373474347422913)
    ·
      refine ⟨7847988092530105760567185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463984123373474347422913 7847988092530105760567185)
      ·
        refine ⟨5885991069397579320425389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7847988092530105760567185 5885991069397579320425389)
        ·
          refine ⟨2207246651024092245159521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5885991069397579320425389 2207246651024092245159521)
          ·
            refine ⟨1655434988268069183869641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207246651024092245159521 1655434988268069183869641)
            ·
              refine ⟨1241576241201051887902231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655434988268069183869641 1241576241201051887902231)
              ·
                refine ⟨1862364361801577831853347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241576241201051887902231 1862364361801577831853347)
                ·
                  refine ⟨2793546542702366747780021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862364361801577831853347 2793546542702366747780021)
                  ·
                    refine ⟨261894988378346882604377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2793546542702366747780021 261894988378346882604377)
                    ·
                      rfl

theorem cell23_1530116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1530116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530116 prefixEnd_1530116 := by exact prefixLift 1530116
  have htrace : WordTrace (prefixWord ++ tailWord_1530116) baseStart_1530116 baseEnd_1530116 := by
    simpa [prefixWord, tailWord_1530116, baseEnd_1530116] using wordTrace_append hprefix tailTrace_1530116
  have hstable : (prefixWord ++ tailWord_1530116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530116).length < 2 ^ (prefixWord ++ tailWord_1530116).sum := by decide
  have hdescent : baseEnd_1530116 < baseStart_1530116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530129 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_1530129 : Nat := 118140960795 + 1530129 * 2 ^ 59
def prefixEnd_1530129 : Nat := 4983230072969 + 3 ^ 40 * 1530129 * 2
def baseEnd_1530129 : Nat := 261897213461183032316857

theorem tailTrace_1530129 : CollatzResearch.WordTrace tailWord_1530129 prefixEnd_1530129 261897213461183032316857 := by
  unfold tailWord_1530129
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808389473611433073145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37205592982407622048763627 55808389473611433073145441)
  ·
    refine ⟨41856292105208574804859081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55808389473611433073145441 41856292105208574804859081)
    ·
      refine ⟨31392219078906431103644311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41856292105208574804859081 31392219078906431103644311)
      ·
        refine ⟨47088328618359646655466467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31392219078906431103644311 47088328618359646655466467)
        ·
          refine ⟨70632492927539469983199701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47088328618359646655466467 70632492927539469983199701)
          ·
            refine ⟨1655449052989206327731243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70632492927539469983199701 1655449052989206327731243)
            ·
              refine ⟨2483173579483809491596865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655449052989206327731243 2483173579483809491596865)
              ·
                refine ⟨1862380184612857118697649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483173579483809491596865 1862380184612857118697649)
                ·
                  refine ⟨1396785138459642839023237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862380184612857118697649 1396785138459642839023237)
                  ·
                    refine ⟨261897213461183032316857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396785138459642839023237 261897213461183032316857)
                    ·
                      rfl

theorem cell23_1530129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_1530129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530129 prefixEnd_1530129 := by exact prefixLift 1530129
  have htrace : WordTrace (prefixWord ++ tailWord_1530129) baseStart_1530129 baseEnd_1530129 := by
    simpa [prefixWord, tailWord_1530129, baseEnd_1530129] using wordTrace_append hprefix tailTrace_1530129
  have hstable : (prefixWord ++ tailWord_1530129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530129).length < 2 ^ (prefixWord ++ tailWord_1530129).sum := by decide
  have hdescent : baseEnd_1530129 < baseStart_1530129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530136 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_1530136 : Nat := 118140960795 + 1530136 * 2 ^ 59
def prefixEnd_1530136 : Nat := 4983230072969 + 3 ^ 40 * 1530136 * 2
def baseEnd_1530136 : Nat := 785695234748130569563039

theorem tailTrace_1530136 : CollatzResearch.WordTrace tailWord_1530136 prefixEnd_1530136 785695234748130569563039 := by
  unfold tailWord_1530136
  simp only [CollatzResearch.WordTrace]
  refine ⟨27904322392293036634325131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37205763189724048845766841 27904322392293036634325131)
  ·
    refine ⟨41856483588439554951487697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27904322392293036634325131 41856483588439554951487697)
    ·
      refine ⟨31392362691329666213615773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41856483588439554951487697 31392362691329666213615773)
      ·
        refine ⟨11772136009248624830105915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31392362691329666213615773 11772136009248624830105915)
        ·
          refine ⟨17658204013872937245158873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772136009248624830105915 17658204013872937245158873)
          ·
            refine ⟨13243653010404702933869155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17658204013872937245158873 13243653010404702933869155)
            ·
              refine ⟨19865479515607054400803733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243653010404702933869155 19865479515607054400803733)
              ·
                refine ⟨931194352294080675037675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19865479515607054400803733 931194352294080675037675)
                ·
                  refine ⟨1396791528441121012556513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931194352294080675037675 1396791528441121012556513)
                  ·
                    refine ⟨1047593646330840759417385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396791528441121012556513 1047593646330840759417385)
                    ·
                      refine ⟨785695234748130569563039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047593646330840759417385 785695234748130569563039)
                      ·
                        rfl

theorem cell23_1530136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_1530136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530136 prefixEnd_1530136 := by exact prefixLift 1530136
  have htrace : WordTrace (prefixWord ++ tailWord_1530136) baseStart_1530136 baseEnd_1530136 := by
    simpa [prefixWord, tailWord_1530136, baseEnd_1530136] using wordTrace_append hprefix tailTrace_1530136
  have hstable : (prefixWord ++ tailWord_1530136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530136).length < 2 ^ (prefixWord ++ tailWord_1530136).sum := by decide
  have hdescent : baseEnd_1530136 < baseStart_1530136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530146 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1530146 : Nat := 118140960795 + 1530146 * 2 ^ 59
def prefixEnd_1530146 : Nat := 4983230072969 + 3 ^ 40 * 1530146 * 2
def baseEnd_1530146 : Nat := 261900123184891843479331

theorem tailTrace_1530146 : CollatzResearch.WordTrace tailWord_1530146 prefixEnd_1530146 261900123184891843479331 := by
  unfold tailWord_1530146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952252378637461244128573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37206006343033229984342861 13952252378637461244128573)
  ·
    refine ⟨5232094641989047966548215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13952252378637461244128573 5232094641989047966548215)
    ·
      refine ⟨7848141962983571949822323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232094641989047966548215 7848141962983571949822323)
      ·
        refine ⟨11772212944475357924733485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848141962983571949822323 11772212944475357924733485)
        ·
          refine ⟨4414579854178259221775057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11772212944475357924733485 4414579854178259221775057)
          ·
            refine ⟨3310934890633694416331293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414579854178259221775057 3310934890633694416331293)
            ·
              refine ⟨1241600583987635406124235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3310934890633694416331293 1241600583987635406124235)
              ·
                refine ⟨1862400875981453109186353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241600583987635406124235 1862400875981453109186353)
                ·
                  refine ⟨1396800656986089831889765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862400875981453109186353 1396800656986089831889765)
                  ·
                    refine ⟨261900123184891843479331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396800656986089831889765 261900123184891843479331)
                    ·
                      rfl

theorem cell23_1530146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1530146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530146 prefixEnd_1530146 := by exact prefixLift 1530146
  have htrace : WordTrace (prefixWord ++ tailWord_1530146) baseStart_1530146 baseEnd_1530146 := by
    simpa [prefixWord, tailWord_1530146, baseEnd_1530146] using wordTrace_append hprefix tailTrace_1530146
  have hstable : (prefixWord ++ tailWord_1530146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530146).length < 2 ^ (prefixWord ++ tailWord_1530146).sum := by decide
  have hdescent : baseEnd_1530146 < baseStart_1530146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530149 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_1530149 : Nat := 118140960795 + 1530149 * 2 ^ 59
def prefixEnd_1530149 : Nat := 4983230072969 + 3 ^ 40 * 1530149 * 2
def baseEnd_1530149 : Nat := 785701909996639018700479

theorem tailTrace_1530149 : CollatzResearch.WordTrace tailWord_1530149 prefixEnd_1530149 785701909996639018700479 := by
  unfold tailWord_1530149
  simp only [CollatzResearch.WordTrace]
  refine ⟨55809118933538976488873501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37206079289025984325915667 55809118933538976488873501)
  ·
    refine ⟨20928419600077116183327563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55809118933538976488873501 20928419600077116183327563)
    ·
      refine ⟨31392629400115674274991345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20928419600077116183327563 31392629400115674274991345)
      ·
        refine ⟨23544472050086755706243509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31392629400115674274991345 23544472050086755706243509)
        ·
          refine ⟨2207294254695633347460329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23544472050086755706243509 2207294254695633347460329)
          ·
            refine ⟨1655470691021725010595247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207294254695633347460329 1655470691021725010595247)
            ·
              refine ⟨2483206036532587515892871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655470691021725010595247 2483206036532587515892871)
              ·
                refine ⟨3724809054798881273839307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483206036532587515892871 3724809054798881273839307)
                ·
                  refine ⟨5587213582198321910758961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724809054798881273839307 5587213582198321910758961)
                  ·
                    refine ⟨4190410186648741433069221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587213582198321910758961 4190410186648741433069221)
                    ·
                      refine ⟨785701909996639018700479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4190410186648741433069221 785701909996639018700479)
                      ·
                        rfl

theorem cell23_1530149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_1530149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530149 prefixEnd_1530149 := by exact prefixLift 1530149
  have htrace : WordTrace (prefixWord ++ tailWord_1530149) baseStart_1530149 baseEnd_1530149 := by
    simpa [prefixWord, tailWord_1530149, baseEnd_1530149] using wordTrace_append hprefix tailTrace_1530149
  have hstable : (prefixWord ++ tailWord_1530149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530149).length < 2 ^ (prefixWord ++ tailWord_1530149).sum := by decide
  have hdescent : baseEnd_1530149 < baseStart_1530149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530165 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1530165 : Nat := 118140960795 + 1530165 * 2 ^ 59
def prefixEnd_1530165 : Nat := 4983230072969 + 3 ^ 40 * 1530165 * 2
def baseEnd_1530165 : Nat := 785710125687110956100405

theorem tailTrace_1530165 : CollatzResearch.WordTrace tailWord_1530165 prefixEnd_1530165 785710125687110956100405 := by
  unfold tailWord_1530165
  simp only [CollatzResearch.WordTrace]
  refine ⟨55809702501481011221455949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37206468334320674147637299 55809702501481011221455949)
  ·
    refine ⟨20928638438055379208045981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55809702501481011221455949 20928638438055379208045981)
    ·
      refine ⟨7848239414270767203017243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20928638438055379208045981 7848239414270767203017243)
      ·
        refine ⟨11772359121406150804525865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848239414270767203017243 11772359121406150804525865)
        ·
          refine ⟨8829269341054613103394399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11772359121406150804525865 8829269341054613103394399)
          ·
            refine ⟨13243904011581919655091599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829269341054613103394399 13243904011581919655091599)
            ·
              refine ⟨19865856017372879482637399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13243904011581919655091599 19865856017372879482637399)
              ·
                refine ⟨29798784026059319223956099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19865856017372879482637399 29798784026059319223956099)
                ·
                  refine ⟨44698176039088978835934149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29798784026059319223956099 44698176039088978835934149)
                  ·
                    refine ⟨8380908007329183531737653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44698176039088978835934149 8380908007329183531737653)
                    ·
                      refine ⟨785710125687110956100405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8380908007329183531737653 785710125687110956100405)
                      ·
                        rfl

theorem cell23_1530165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1530165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530165 prefixEnd_1530165 := by exact prefixLift 1530165
  have htrace : WordTrace (prefixWord ++ tailWord_1530165) baseStart_1530165 baseEnd_1530165 := by
    simpa [prefixWord, tailWord_1530165, baseEnd_1530165] using wordTrace_append hprefix tailTrace_1530165
  have hstable : (prefixWord ++ tailWord_1530165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530165).length < 2 ^ (prefixWord ++ tailWord_1530165).sum := by decide
  have hdescent : baseEnd_1530165 < baseStart_1530165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530169 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1530169 : Nat := 118140960795 + 1530169 * 2 ^ 59
def prefixEnd_1530169 : Nat := 4983230072969 + 3 ^ 40 * 1530169 * 2
def baseEnd_1530169 : Nat := 785712179609728940450387

theorem tailTrace_1530169 : CollatzResearch.WordTrace tailWord_1530169 prefixEnd_1530169 785712179609728940450387 := by
  unfold tailWord_1530169
  simp only [CollatzResearch.WordTrace]
  refine ⟨55809848393466519904601561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37206565595644346603067707 55809848393466519904601561)
  ·
    refine ⟨41857386295099889928451171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55809848393466519904601561 41857386295099889928451171)
    ·
      refine ⟨62786079442649834892676757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41857386295099889928451171 62786079442649834892676757)
      ·
        refine ⟨2943097473874211010594223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62786079442649834892676757 2943097473874211010594223)
        ·
          refine ⟨4414646210811316515891335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943097473874211010594223 4414646210811316515891335)
          ·
            refine ⟨6621969316216974773837003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414646210811316515891335 6621969316216974773837003)
            ·
              refine ⟨9932953974325462160755505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621969316216974773837003 9932953974325462160755505)
              ·
                refine ⟨7449715480744096620566629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9932953974325462160755505 7449715480744096620566629)
                ·
                  refine ⟨1396821652639518116356243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7449715480744096620566629 1396821652639518116356243)
                  ·
                    refine ⟨2095232478959277174534365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1396821652639518116356243 2095232478959277174534365)
                    ·
                      refine ⟨785712179609728940450387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2095232478959277174534365 785712179609728940450387)
                      ·
                        rfl

theorem cell23_1530169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1530169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530169 prefixEnd_1530169 := by exact prefixLift 1530169
  have htrace : WordTrace (prefixWord ++ tailWord_1530169) baseStart_1530169 baseEnd_1530169 := by
    simpa [prefixWord, tailWord_1530169, baseEnd_1530169] using wordTrace_append hprefix tailTrace_1530169
  have hstable : (prefixWord ++ tailWord_1530169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530169).length < 2 ^ (prefixWord ++ tailWord_1530169).sum := by decide
  have hdescent : baseEnd_1530169 < baseStart_1530169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530179 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 1, 3, 2]
def baseStart_1530179 : Nat := 118140960795 + 1530179 * 2 ^ 59
def prefixEnd_1530179 : Nat := 4983230072969 + 3 ^ 40 * 1530179 * 2
def baseEnd_1530179 : Nat := 785717314416273901325341

theorem tailTrace_1530179 : CollatzResearch.WordTrace tailWord_1530179 prefixEnd_1530179 785717314416273901325341 := by
  unfold tailWord_1530179
  simp only [CollatzResearch.WordTrace]
  refine ⟨55810213123430291612465591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37206808748953527741643727 55810213123430291612465591)
  ·
    refine ⟨83715319685145437418698387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55810213123430291612465591 83715319685145437418698387)
    ·
      refine ⟨125572979527718156128047581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83715319685145437418698387 125572979527718156128047581)
      ·
        refine ⟨47089867322894308548017843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125572979527718156128047581 47089867322894308548017843)
        ·
          refine ⟨70634800984341462822026765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47089867322894308548017843 70634800984341462822026765)
          ·
            refine ⟨26488050369128048558260037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70634800984341462822026765 26488050369128048558260037)
            ·
              refine ⟨4966509444211509104673757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26488050369128048558260037 4966509444211509104673757)
              ·
                refine ⟨1862441041579315914252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4966509444211509104673757 1862441041579315914252659)
                ·
                  refine ⟨2793661562368973871378989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862441041579315914252659 2793661562368973871378989)
                  ·
                    refine ⟨1047623085888365201767121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2793661562368973871378989 1047623085888365201767121)
                    ·
                      refine ⟨785717314416273901325341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047623085888365201767121 785717314416273901325341)
                      ·
                        rfl

theorem cell23_1530179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_1530179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530179 prefixEnd_1530179 := by exact prefixLift 1530179
  have htrace : WordTrace (prefixWord ++ tailWord_1530179) baseStart_1530179 baseEnd_1530179 := by
    simpa [prefixWord, tailWord_1530179, baseEnd_1530179] using wordTrace_append hprefix tailTrace_1530179
  have hstable : (prefixWord ++ tailWord_1530179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530179).length < 2 ^ (prefixWord ++ tailWord_1530179).sum := by decide
  have hdescent : baseEnd_1530179 < baseStart_1530179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530243 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 2, 2, 2]
def baseStart_1530243 : Nat := 118140960795 + 1530243 * 2 ^ 59
def prefixEnd_1530243 : Nat := 4983230072969 + 3 ^ 40 * 1530243 * 2
def baseEnd_1530243 : Nat := 785750177178161650925047

theorem tailTrace_1530243 : CollatzResearch.WordTrace tailWord_1530243 prefixEnd_1530243 785750177178161650925047 := by
  unfold tailWord_1530243
  simp only [CollatzResearch.WordTrace]
  refine ⟨55812547395198430542795383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37208364930132287028530255 55812547395198430542795383)
  ·
    refine ⟨83718821092797645814193075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55812547395198430542795383 83718821092797645814193075)
    ·
      refine ⟨125578231639196468721289613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83718821092797645814193075 125578231639196468721289613)
      ·
        refine ⟨47091836864698675770483605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125578231639196468721289613 47091836864698675770483605)
        ·
          refine ⟨2207429853032750426741419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47091836864698675770483605 2207429853032750426741419)
          ·
            refine ⟨3311144779549125640112129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207429853032750426741419 3311144779549125640112129)
            ·
              refine ⟨2483358584661844230084097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3311144779549125640112129 2483358584661844230084097)
              ·
                refine ⟨1862518938496383172563073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483358584661844230084097 1862518938496383172563073)
                ·
                  refine ⟨1396889203872287379422305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862518938496383172563073 1396889203872287379422305)
                  ·
                    refine ⟨1047666902904215534566729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396889203872287379422305 1047666902904215534566729)
                    ·
                      refine ⟨785750177178161650925047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047666902904215534566729 785750177178161650925047)
                      ·
                        rfl

theorem cell23_1530243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_1530243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530243 prefixEnd_1530243 := by exact prefixLift 1530243
  have htrace : WordTrace (prefixWord ++ tailWord_1530243) baseStart_1530243 baseEnd_1530243 := by
    simpa [prefixWord, tailWord_1530243, baseEnd_1530243] using wordTrace_append hprefix tailTrace_1530243
  have hstable : (prefixWord ++ tailWord_1530243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530243).length < 2 ^ (prefixWord ++ tailWord_1530243).sum := by decide
  have hdescent : baseEnd_1530243 < baseStart_1530243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530245 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1530245 : Nat := 118140960795 + 1530245 * 2 ^ 59
def prefixEnd_1530245 : Nat := 4983230072969 + 3 ^ 40 * 1530245 * 2
def baseEnd_1530245 : Nat := 261917068046490214366679

theorem tailTrace_1530245 : CollatzResearch.WordTrace tailWord_1530245 prefixEnd_1530245 261917068046490214366679 := by
  unfold tailWord_1530245
  simp only [CollatzResearch.WordTrace]
  refine ⟨55812620341191184884368189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37208413560794123256245459 55812620341191184884368189)
  ·
    refine ⟨20929732627946694331638071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55812620341191184884368189 20929732627946694331638071)
    ·
      refine ⟨31394598941920041497457107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20929732627946694331638071 31394598941920041497457107)
      ·
        refine ⟨47091898412880062246185661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31394598941920041497457107 47091898412880062246185661)
        ·
          refine ⟨17659461904830023342319623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47091898412880062246185661 17659461904830023342319623)
          ·
            refine ⟨26489192857245035013479435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17659461904830023342319623 26489192857245035013479435)
            ·
              refine ⟨39733789285867552520219153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26489192857245035013479435 39733789285867552520219153)
              ·
                refine ⟨29800341964400664390164365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39733789285867552520219153 29800341964400664390164365)
                ·
                  refine ⟨11175128236650249146311637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29800341964400664390164365 11175128236650249146311637)
                  ·
                    refine ⟨261917068046490214366679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11175128236650249146311637 261917068046490214366679)
                    ·
                      rfl

theorem cell23_1530245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1530245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530245 prefixEnd_1530245 := by exact prefixLift 1530245
  have htrace : WordTrace (prefixWord ++ tailWord_1530245) baseStart_1530245 baseEnd_1530245 := by
    simpa [prefixWord, tailWord_1530245, baseEnd_1530245] using wordTrace_append hprefix tailTrace_1530245
  have hstable : (prefixWord ++ tailWord_1530245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530245).length < 2 ^ (prefixWord ++ tailWord_1530245).sum := by decide
  have hdescent : baseEnd_1530245 < baseStart_1530245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530249 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 5]
def baseStart_1530249 : Nat := 118140960795 + 1530249 * 2 ^ 59
def prefixEnd_1530249 : Nat := 4983230072969 + 3 ^ 40 * 1530249 * 2
def baseEnd_1530249 : Nat := 87305917562454291938891

theorem tailTrace_1530249 : CollatzResearch.WordTrace tailWord_1530249 prefixEnd_1530249 87305917562454291938891 := by
  unfold tailWord_1530249
  simp only [CollatzResearch.WordTrace]
  refine ⟨55812766233176693567513801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37208510822117795711675867 55812766233176693567513801)
  ·
    refine ⟨41859574674882520175635351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55812766233176693567513801 41859574674882520175635351)
    ·
      refine ⟨62789362012323780263453027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41859574674882520175635351 62789362012323780263453027)
      ·
        refine ⟨94184043018485670395179541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62789362012323780263453027 94184043018485670395179541)
        ·
          refine ⟨4414877016491515799774041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94184043018485670395179541 4414877016491515799774041)
          ·
            refine ⟨3311157762368636849830531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414877016491515799774041 3311157762368636849830531)
            ·
              refine ⟨4966736643552955274745797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311157762368636849830531 4966736643552955274745797)
              ·
                refine ⟨931263120666179114014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4966736643552955274745797 931263120666179114014837)
                ·
                  refine ⟨87305917562454291938891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931263120666179114014837 87305917562454291938891)
                  ·
                    rfl

theorem cell23_1530249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 5].length) (baseStart_1530249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530249 prefixEnd_1530249 := by exact prefixLift 1530249
  have htrace : WordTrace (prefixWord ++ tailWord_1530249) baseStart_1530249 baseEnd_1530249 := by
    simpa [prefixWord, tailWord_1530249, baseEnd_1530249] using wordTrace_append hprefix tailTrace_1530249
  have hstable : (prefixWord ++ tailWord_1530249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530249).length < 2 ^ (prefixWord ++ tailWord_1530249).sum := by decide
  have hdescent : baseEnd_1530249 < baseStart_1530249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530279 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1530279 : Nat := 118140960795 + 1530279 * 2 ^ 59
def prefixEnd_1530279 : Nat := 4983230072969 + 3 ^ 40 * 1530279 * 2
def baseEnd_1530279 : Nat := 261922887493907836691627

theorem tailTrace_1530279 : CollatzResearch.WordTrace tailWord_1530279 prefixEnd_1530279 261922887493907836691627 := by
  unfold tailWord_1530279
  simp only [CollatzResearch.WordTrace]
  refine ⟨55813860423068008691105891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37209240282045339127403927 55813860423068008691105891)
  ·
    refine ⟨83720790634602013036658837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55813860423068008691105891 83720790634602013036658837)
    ·
      refine ⟨3924412060996969361093383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83720790634602013036658837 3924412060996969361093383)
      ·
        refine ⟨5886618091495454041640075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924412060996969361093383 5886618091495454041640075)
        ·
          refine ⟨8829927137243181062460113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886618091495454041640075 8829927137243181062460113)
          ·
            refine ⟨6622445352932385796845085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8829927137243181062460113 6622445352932385796845085)
            ·
              refine ⟨2483417007349644673816907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6622445352932385796845085 2483417007349644673816907)
              ·
                refine ⟨3725125511024467010725361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483417007349644673816907 3725125511024467010725361)
                ·
                  refine ⟨2793844133268350258044021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3725125511024467010725361 2793844133268350258044021)
                  ·
                    refine ⟨261922887493907836691627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2793844133268350258044021 261922887493907836691627)
                    ·
                      rfl

theorem cell23_1530279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1530279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530279 prefixEnd_1530279 := by exact prefixLift 1530279
  have htrace : WordTrace (prefixWord ++ tailWord_1530279) baseStart_1530279 baseEnd_1530279 := by
    simpa [prefixWord, tailWord_1530279, baseEnd_1530279] using wordTrace_append hprefix tailTrace_1530279
  have hstable : (prefixWord ++ tailWord_1530279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530279).length < 2 ^ (prefixWord ++ tailWord_1530279).sum := by decide
  have hdescent : baseEnd_1530279 < baseStart_1530279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530302 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1530302 : Nat := 118140960795 + 1530302 * 2 ^ 59
def prefixEnd_1530302 : Nat := 4983230072969 + 3 ^ 40 * 1530302 * 2
def baseEnd_1530302 : Nat := 785780472536776920087275

theorem tailTrace_1530302 : CollatzResearch.WordTrace tailWord_1530302 prefixEnd_1530302 785780472536776920087275 := by
  unfold tailWord_1530302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976837412748085452399145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37209799534656455746128773 6976837412748085452399145)
  ·
    refine ⟨5232628059561064089299359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6976837412748085452399145 5232628059561064089299359)
    ·
      refine ⟨7848942089341596133949039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232628059561064089299359 7848942089341596133949039)
      ·
        refine ⟨11773413134012394200923559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848942089341596133949039 11773413134012394200923559)
        ·
          refine ⟨17660119701018591301385339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11773413134012394200923559 17660119701018591301385339)
          ·
            refine ⟨26490179551527886952078009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17660119701018591301385339 26490179551527886952078009)
            ·
              refine ⟨19867634663645915214058507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26490179551527886952078009 19867634663645915214058507)
              ·
                refine ⟨29801451995468872821087761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19867634663645915214058507 29801451995468872821087761)
                ·
                  refine ⟨22351088996601654615815821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29801451995468872821087761 22351088996601654615815821)
                  ·
                    refine ⟨8381658373725620480930933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22351088996601654615815821 8381658373725620480930933)
                    ·
                      refine ⟨785780472536776920087275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8381658373725620480930933 785780472536776920087275)
                      ·
                        rfl

theorem cell23_1530302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1530302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530302 prefixEnd_1530302 := by exact prefixLift 1530302
  have htrace : WordTrace (prefixWord ++ tailWord_1530302) baseStart_1530302 baseEnd_1530302 := by
    simpa [prefixWord, tailWord_1530302, baseEnd_1530302] using wordTrace_append hprefix tailTrace_1530302
  have hstable : (prefixWord ++ tailWord_1530302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530302).length < 2 ^ (prefixWord ++ tailWord_1530302).sum := by decide
  have hdescent : baseEnd_1530302 < baseStart_1530302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530326 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1530326 : Nat := 118140960795 + 1530326 * 2 ^ 59
def prefixEnd_1530326 : Nat := 4983230072969 + 3 ^ 40 * 1530326 * 2
def baseEnd_1530326 : Nat := 261930932024161608729055

theorem tailTrace_1530326 : CollatzResearch.WordTrace tailWord_1530326 prefixEnd_1530326 261930932024161608729055 := by
  unfold tailWord_1530326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488473415868608482379177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37210383102598490478711221 3488473415868608482379177)
  ·
    refine ⟨2616355061901456361784383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3488473415868608482379177 2616355061901456361784383)
    ·
      refine ⟨3924532592852184542676575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616355061901456361784383 3924532592852184542676575)
      ·
        refine ⟨5886798889278276814014863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924532592852184542676575 5886798889278276814014863)
        ·
          refine ⟨8830198333917415221022295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886798889278276814014863 8830198333917415221022295)
          ·
            refine ⟨13245297500876122831533443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830198333917415221022295 13245297500876122831533443)
            ·
              refine ⟨19867946251314184247300165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13245297500876122831533443 19867946251314184247300165)
              ·
                refine ⟨3725239922121409546368781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19867946251314184247300165 3725239922121409546368781)
                ·
                  refine ⟨1396964970795528579888293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3725239922121409546368781 1396964970795528579888293)
                  ·
                    refine ⟨261930932024161608729055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396964970795528579888293 261930932024161608729055)
                    ·
                      rfl

theorem cell23_1530326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1530326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530326 prefixEnd_1530326 := by exact prefixLift 1530326
  have htrace : WordTrace (prefixWord ++ tailWord_1530326) baseStart_1530326 baseEnd_1530326 := by
    simpa [prefixWord, tailWord_1530326, baseEnd_1530326] using wordTrace_append hprefix tailTrace_1530326
  have hstable : (prefixWord ++ tailWord_1530326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530326).length < 2 ^ (prefixWord ++ tailWord_1530326).sum := by decide
  have hdescent : baseEnd_1530326 < baseStart_1530326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530389 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1530389 : Nat := 118140960795 + 1530389 * 2 ^ 59
def prefixEnd_1530389 : Nat := 4983230072969 + 3 ^ 40 * 1530389 * 2
def baseEnd_1530389 : Nat := 785825145353718079699375

theorem tailTrace_1530389 : CollatzResearch.WordTrace tailWord_1530389 prefixEnd_1530389 785825145353718079699375 := by
  unfold tailWord_1530389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55817872452669497477610221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37211914968446331651740147 55817872452669497477610221)
  ·
    refine ⟨20931702169751061554103833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55817872452669497477610221 20931702169751061554103833)
    ·
      refine ⟨15698776627313296165577875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20931702169751061554103833 15698776627313296165577875)
      ·
        refine ⟨23548164940969944248366813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15698776627313296165577875 23548164940969944248366813)
        ·
          refine ⟨8830561852863729093137555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23548164940969944248366813 8830561852863729093137555)
          ·
            refine ⟨13245842779295593639706333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830561852863729093137555 13245842779295593639706333)
            ·
              refine ⟨4967191042235847614889875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13245842779295593639706333 4967191042235847614889875)
              ·
                refine ⟨7450786563353771422334813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967191042235847614889875 7450786563353771422334813)
                ·
                  refine ⟨2794044961257664283375555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7450786563353771422334813 2794044961257664283375555)
                  ·
                    refine ⟨4191067441886496425063333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2794044961257664283375555 4191067441886496425063333)
                    ·
                      refine ⟨785825145353718079699375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4191067441886496425063333 785825145353718079699375)
                      ·
                        rfl

theorem cell23_1530389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1530389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530389 prefixEnd_1530389 := by exact prefixLift 1530389
  have htrace : WordTrace (prefixWord ++ tailWord_1530389) baseStart_1530389 baseEnd_1530389 := by
    simpa [prefixWord, tailWord_1530389, baseEnd_1530389] using wordTrace_append hprefix tailTrace_1530389
  have hstable : (prefixWord ++ tailWord_1530389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530389).length < 2 ^ (prefixWord ++ tailWord_1530389).sum := by decide
  have hdescent : baseEnd_1530389 < baseStart_1530389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530429 : List Nat := [1, 4, 1, 3, 2, 1, 3, 8]
def baseStart_1530429 : Nat := 118140960795 + 1530429 * 2 ^ 59
def prefixEnd_1530429 : Nat := 4983230072969 + 3 ^ 40 * 1530429 * 2
def baseEnd_1530429 : Nat := 29105395725181404562933

theorem tailTrace_1530429 : CollatzResearch.WordTrace tailWord_1530429 prefixEnd_1530429 29105395725181404562933 := by
  unfold tailWord_1530429
  simp only [CollatzResearch.WordTrace]
  refine ⟨55819331372524584309066341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37212887581683056206044227 55819331372524584309066341)
  ·
    refine ⟨10466124632348359557949939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55819331372524584309066341 10466124632348359557949939)
    ·
      refine ⟨15699186948522539336924909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10466124632348359557949939 15699186948522539336924909)
      ·
        refine ⟨5887195105695952251346841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15699186948522539336924909 5887195105695952251346841)
        ·
          refine ⟨4415396329271964188510131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5887195105695952251346841 4415396329271964188510131)
          ·
            refine ⟨6623094493907946282765197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415396329271964188510131 6623094493907946282765197)
            ·
              refine ⟨2483660435215479856036949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6623094493907946282765197 2483660435215479856036949)
              ·
                refine ⟨29105395725181404562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2483660435215479856036949 29105395725181404562933)
                ·
                  rfl

theorem cell23_1530429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 8].length) (baseStart_1530429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530429 prefixEnd_1530429 := by exact prefixLift 1530429
  have htrace : WordTrace (prefixWord ++ tailWord_1530429) baseStart_1530429 baseEnd_1530429 := by
    simpa [prefixWord, tailWord_1530429, baseEnd_1530429] using wordTrace_append hprefix tailTrace_1530429
  have hstable : (prefixWord ++ tailWord_1530429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530429).length < 2 ^ (prefixWord ++ tailWord_1530429).sum := by decide
  have hdescent : baseEnd_1530429 < baseStart_1530429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530432 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1530432 : Nat := 118140960795 + 1530432 * 2 ^ 59
def prefixEnd_1530432 : Nat := 4983230072969 + 3 ^ 40 * 1530432 * 2
def baseEnd_1530432 : Nat := 785847225021861411461677

theorem tailTrace_1530432 : CollatzResearch.WordTrace tailWord_1530432 prefixEnd_1530432 785847225021861411461677 := by
  unfold tailWord_1530432
  simp only [CollatzResearch.WordTrace]
  refine ⟨27909720395756857910712775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37212960527675810547617033 27909720395756857910712775)
  ·
    refine ⟨41864580593635286866069163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27909720395756857910712775 41864580593635286866069163)
    ·
      refine ⟨62796870890452930299103745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41864580593635286866069163 62796870890452930299103745)
      ·
        refine ⟨47097653167839697724327809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62796870890452930299103745 47097653167839697724327809)
        ·
          refine ⟨35323239875879773293245857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47097653167839697724327809 35323239875879773293245857)
          ·
            refine ⟨26492429906909829969934393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35323239875879773293245857 26492429906909829969934393)
            ·
              refine ⟨19869322430182372477450795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26492429906909829969934393 19869322430182372477450795)
              ·
                refine ⟨29803983645273558716176193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19869322430182372477450795 29803983645273558716176193)
                ·
                  refine ⟨22352987733955169037132145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29803983645273558716176193 22352987733955169037132145)
                  ·
                    refine ⟨16764740800466376777849109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22352987733955169037132145 16764740800466376777849109)
                    ·
                      refine ⟨785847225021861411461677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16764740800466376777849109 785847225021861411461677)
                      ·
                        rfl

theorem cell23_1530432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1530432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530432 prefixEnd_1530432 := by exact prefixLift 1530432
  have htrace : WordTrace (prefixWord ++ tailWord_1530432) baseStart_1530432 baseEnd_1530432 := by
    simpa [prefixWord, tailWord_1530432, baseEnd_1530432] using wordTrace_append hprefix tailTrace_1530432
  have hstable : (prefixWord ++ tailWord_1530432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530432).length < 2 ^ (prefixWord ++ tailWord_1530432).sum := by decide
  have hdescent : baseEnd_1530432 < baseStart_1530432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530489 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_1530489 : Nat := 118140960795 + 1530489 * 2 ^ 59
def prefixEnd_1530489 : Nat := 4983230072969 + 3 ^ 40 * 1530489 * 2
def baseEnd_1530489 : Nat := 261958831139722562816305

theorem tailTrace_1530489 : CollatzResearch.WordTrace tailWord_1530489 prefixEnd_1530489 261958831139722562816305 := by
  unfold tailWord_1530489
  simp only [CollatzResearch.WordTrace]
  refine ⟨55821519752307214556250521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37214346501538143037500347 55821519752307214556250521)
  ·
    refine ⟨41866139814230410917187891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55821519752307214556250521 41866139814230410917187891)
    ·
      refine ⟨62799209721345616375781837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41866139814230410917187891 62799209721345616375781837)
      ·
        refine ⟨23549703645504606140918189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62799209721345616375781837 23549703645504606140918189)
        ·
          refine ⟨8831138867064227302844321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23549703645504606140918189 8831138867064227302844321)
          ·
            refine ⟨6623354150298170477133241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8831138867064227302844321 6623354150298170477133241)
            ·
              refine ⟨4967515612723627857849931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623354150298170477133241 4967515612723627857849931)
              ·
                refine ⟨7451273419085441786774897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967515612723627857849931 7451273419085441786774897)
                ·
                  refine ⟨5588455064314081340081173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7451273419085441786774897 5588455064314081340081173)
                  ·
                    refine ⟨261958831139722562816305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5588455064314081340081173 261958831139722562816305)
                    ·
                      rfl

theorem cell23_1530489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_1530489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530489 prefixEnd_1530489 := by exact prefixLift 1530489
  have htrace : WordTrace (prefixWord ++ tailWord_1530489) baseStart_1530489 baseEnd_1530489 := by
    simpa [prefixWord, tailWord_1530489, baseEnd_1530489] using wordTrace_append hprefix tailTrace_1530489
  have hstable : (prefixWord ++ tailWord_1530489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530489).length < 2 ^ (prefixWord ++ tailWord_1530489).sum := by decide
  have hdescent : baseEnd_1530489 < baseStart_1530489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530499 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1530499 : Nat := 118140960795 + 1530499 * 2 ^ 59
def prefixEnd_1530499 : Nat := 4983230072969 + 3 ^ 40 * 1530499 * 2
def baseEnd_1530499 : Nat := 785881628225712649323869

theorem tailTrace_1530499 : CollatzResearch.WordTrace tailWord_1530499 prefixEnd_1530499 785881628225712649323869 := by
  unfold tailWord_1530499
  simp only [CollatzResearch.WordTrace]
  refine ⟨55821884482270986264114551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37214589654847324176076367 55821884482270986264114551)
  ·
    refine ⟨83732826723406479396171827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55821884482270986264114551 83732826723406479396171827)
    ·
      refine ⟨125599240085109719094257741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83732826723406479396171827 125599240085109719094257741)
      ·
        refine ⟨47099715031916144660346653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125599240085109719094257741 47099715031916144660346653)
        ·
          refine ⟨17662393136968554247629995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47099715031916144660346653 17662393136968554247629995)
          ·
            refine ⟨26493589705452831371444993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17662393136968554247629995 26493589705452831371444993)
            ·
              refine ⟨19870192279089623528583745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26493589705452831371444993 19870192279089623528583745)
              ·
                refine ⟨14902644209317217646437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19870192279089623528583745 14902644209317217646437809)
                ·
                  refine ⟨11176983156987913234828357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14902644209317217646437809 11176983156987913234828357)
                  ·
                    refine ⟨2095684341935233731530317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11176983156987913234828357 2095684341935233731530317)
                    ·
                      refine ⟨785881628225712649323869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2095684341935233731530317 785881628225712649323869)
                      ·
                        rfl

theorem cell23_1530499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1530499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530499 prefixEnd_1530499 := by exact prefixLift 1530499
  have htrace : WordTrace (prefixWord ++ tailWord_1530499) baseStart_1530499 baseEnd_1530499 := by
    simpa [prefixWord, tailWord_1530499, baseEnd_1530499] using wordTrace_append hprefix tailTrace_1530499
  have hstable : (prefixWord ++ tailWord_1530499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530499).length < 2 ^ (prefixWord ++ tailWord_1530499).sum := by decide
  have hdescent : baseEnd_1530499 < baseStart_1530499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530500 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1530500 : Nat := 118140960795 + 1530500 * 2 ^ 59
def prefixEnd_1530500 : Nat := 4983230072969 + 3 ^ 40 * 1530500 * 2
def baseEnd_1530500 : Nat := 785882141706367145411365

theorem tailTrace_1530500 : CollatzResearch.WordTrace tailWord_1530500 prefixEnd_1530500 785882141706367145411365 := by
  unfold tailWord_1530500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910960477633681717450477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37214613970178242289933969 27910960477633681717450477)
  ·
    refine ⟨10466610179112630644043929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27910960477633681717450477 10466610179112630644043929)
    ·
      refine ⟨7849957634334472983032947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10466610179112630644043929 7849957634334472983032947)
      ·
        refine ⟨11774936451501709474549421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849957634334472983032947 11774936451501709474549421)
        ·
          refine ⟨4415601169313141052956033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11774936451501709474549421 4415601169313141052956033)
          ·
            refine ⟨3311700876984855789717025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4415601169313141052956033 3311700876984855789717025)
            ·
              refine ⟨2483775657738641842287769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3311700876984855789717025 2483775657738641842287769)
              ·
                refine ⟨1862831743303981381715827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483775657738641842287769 1862831743303981381715827)
                ·
                  refine ⟨2794247614955972072573741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862831743303981381715827 2794247614955972072573741)
                  ·
                    refine ⟨1047842855608489527215153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794247614955972072573741 1047842855608489527215153)
                    ·
                      refine ⟨785882141706367145411365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047842855608489527215153 785882141706367145411365)
                      ·
                        rfl

theorem cell23_1530500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1530500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530500 prefixEnd_1530500 := by exact prefixLift 1530500
  have htrace : WordTrace (prefixWord ++ tailWord_1530500) baseStart_1530500 baseEnd_1530500 := by
    simpa [prefixWord, tailWord_1530500, baseEnd_1530500] using wordTrace_append hprefix tailTrace_1530500
  have hstable : (prefixWord ++ tailWord_1530500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530500).length < 2 ^ (prefixWord ++ tailWord_1530500).sum := by decide
  have hdescent : baseEnd_1530500 < baseStart_1530500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530516 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1530516 : Nat := 118140960795 + 1530516 * 2 ^ 59
def prefixEnd_1530516 : Nat := 4983230072969 + 3 ^ 40 * 1530516 * 2
def baseEnd_1530516 : Nat := 785890357396839082811291

theorem tailTrace_1530516 : CollatzResearch.WordTrace tailWord_1530516 prefixEnd_1530516 785890357396839082811291 := by
  unfold tailWord_1530516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27911252261604699083741701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37215003015472932111655601 27911252261604699083741701)
  ·
    refine ⟨5233359799050881078201569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27911252261604699083741701 5233359799050881078201569)
    ·
      refine ⟨3925019849288160808651177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5233359799050881078201569 3925019849288160808651177)
      ·
        refine ⟨2943764886966120606488383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925019849288160808651177 2943764886966120606488383)
        ·
          refine ⟨4415647330449180909732575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943764886966120606488383 4415647330449180909732575)
          ·
            refine ⟨6623470995673771364598863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415647330449180909732575 6623470995673771364598863)
            ·
              refine ⟨9935206493510657046898295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623470995673771364598863 9935206493510657046898295)
              ·
                refine ⟨14902809740265985570347443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9935206493510657046898295 14902809740265985570347443)
                ·
                  refine ⟨22354214610398978355521165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14902809740265985570347443 22354214610398978355521165)
                  ·
                    refine ⟨8382830478899616883320437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22354214610398978355521165 8382830478899616883320437)
                    ·
                      refine ⟨785890357396839082811291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8382830478899616883320437 785890357396839082811291)
                      ·
                        rfl

theorem cell23_1530516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1530516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530516 prefixEnd_1530516 := by exact prefixLift 1530516
  have htrace : WordTrace (prefixWord ++ tailWord_1530516) baseStart_1530516 baseEnd_1530516 := by
    simpa [prefixWord, tailWord_1530516, baseEnd_1530516] using wordTrace_append hprefix tailTrace_1530516
  have hstable : (prefixWord ++ tailWord_1530516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530516).length < 2 ^ (prefixWord ++ tailWord_1530516).sum := by decide
  have hdescent : baseEnd_1530516 < baseStart_1530516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530547 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 2, 2, 2]
def baseStart_1530547 : Nat := 118140960795 + 1530547 * 2 ^ 59
def prefixEnd_1530547 : Nat := 4983230072969 + 3 ^ 40 * 1530547 * 2
def baseEnd_1530547 : Nat := 785906275297128461523649

theorem tailTrace_1530547 : CollatzResearch.WordTrace tailWord_1530547 prefixEnd_1530547 785906275297128461523649 := by
  unfold tailWord_1530547
  simp only [CollatzResearch.WordTrace]
  refine ⟨55823635186097090461861895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37215756790731393641241263 55823635186097090461861895)
  ·
    refine ⟨83735452779145635692792843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55823635186097090461861895 83735452779145635692792843)
    ·
      refine ⟨125603179168718453539189265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83735452779145635692792843 125603179168718453539189265)
      ·
        refine ⟨94202384376538840154391949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125603179168718453539189265 94202384376538840154391949)
        ·
          refine ⟨35325894141202065057896981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94202384376538840154391949 35325894141202065057896981)
          ·
            refine ⟨1655901287868846799588921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35325894141202065057896981 1655901287868846799588921)
            ·
              refine ⟨1241925965901635099691691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655901287868846799588921 1241925965901635099691691)
              ·
                refine ⟨1862888948852452649537537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241925965901635099691691 1862888948852452649537537)
                ·
                  refine ⟨1397166711639339487153153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862888948852452649537537 1397166711639339487153153)
                  ·
                    refine ⟨1047875033729504615364865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1397166711639339487153153 1047875033729504615364865)
                    ·
                      refine ⟨785906275297128461523649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1047875033729504615364865 785906275297128461523649)
                      ·
                        rfl

theorem cell23_1530547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 2, 2].length) (baseStart_1530547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530547 prefixEnd_1530547 := by exact prefixLift 1530547
  have htrace : WordTrace (prefixWord ++ tailWord_1530547) baseStart_1530547 baseEnd_1530547 := by
    simpa [prefixWord, tailWord_1530547, baseEnd_1530547] using wordTrace_append hprefix tailTrace_1530547
  have hstable : (prefixWord ++ tailWord_1530547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530547).length < 2 ^ (prefixWord ++ tailWord_1530547).sum := by decide
  have hdescent : baseEnd_1530547 < baseStart_1530547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530586 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1530586 : Nat := 118140960795 + 1530586 * 2 ^ 59
def prefixEnd_1530586 : Nat := 4983230072969 + 3 ^ 40 * 1530586 * 2
def baseEnd_1530586 : Nat := 785926301042653808935969

theorem tailTrace_1530586 : CollatzResearch.WordTrace tailWord_1530586 prefixEnd_1530586 785926301042653808935969 := by
  unfold tailWord_1530586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13956264408238950030632903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37216705088637200081687741 13956264408238950030632903)
  ·
    refine ⟨20934396612358425045949355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13956264408238950030632903 20934396612358425045949355)
    ·
      refine ⟨31401594918537637568924033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20934396612358425045949355 31401594918537637568924033)
      ·
        refine ⟨23551196188903228176693025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31401594918537637568924033 23551196188903228176693025)
        ·
          refine ⟨17663397141677421132519769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23551196188903228176693025 17663397141677421132519769)
          ·
            refine ⟨13247547856258065849389827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17663397141677421132519769 13247547856258065849389827)
            ·
              refine ⟨19871321784387098774084741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13247547856258065849389827 19871321784387098774084741)
              ·
                refine ⟨3725872834572581020140889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19871321784387098774084741 3725872834572581020140889)
                ·
                  refine ⟨2794404625929435765105667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3725872834572581020140889 2794404625929435765105667)
                  ·
                    refine ⟨4191606938894153647658501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2794404625929435765105667 4191606938894153647658501)
                    ·
                      refine ⟨785926301042653808935969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4191606938894153647658501 785926301042653808935969)
                      ·
                        rfl

theorem cell23_1530586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1530586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530586 prefixEnd_1530586 := by exact prefixLift 1530586
  have htrace : WordTrace (prefixWord ++ tailWord_1530586) baseStart_1530586 baseEnd_1530586 := by
    simpa [prefixWord, tailWord_1530586, baseEnd_1530586] using wordTrace_append hprefix tailTrace_1530586
  have hstable : (prefixWord ++ tailWord_1530586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530586).length < 2 ^ (prefixWord ++ tailWord_1530586).sum := by decide
  have hdescent : baseEnd_1530586 < baseStart_1530586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1530629 : Nat := 118140960795 + 1530629 * 2 ^ 59
def prefixEnd_1530629 : Nat := 4983230072969 + 3 ^ 40 * 1530629 * 2
def baseEnd_1530629 : Nat := 785948380710797140698271

theorem tailTrace_1530629 : CollatzResearch.WordTrace tailWord_1530629 prefixEnd_1530629 785948380710797140698271 := by
  unfold tailWord_1530629
  simp only [CollatzResearch.WordTrace]
  refine ⟨55826625971800018466346941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37217750647866678977564627 55826625971800018466346941)
  ·
    refine ⟨20934984739425006924880103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55826625971800018466346941 20934984739425006924880103)
    ·
      refine ⟨31402477109137510387320155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20934984739425006924880103 31402477109137510387320155)
      ·
        refine ⟨47103715663706265580980233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31402477109137510387320155 47103715663706265580980233)
        ·
          refine ⟨35327786747779699185735175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47103715663706265580980233 35327786747779699185735175)
          ·
            refine ⟨52991680121669548778602763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35327786747779699185735175 52991680121669548778602763)
            ·
              refine ⟨79487520182504323167904145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52991680121669548778602763 79487520182504323167904145)
              ·
                refine ⟨59615640136878242375928109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79487520182504323167904145 59615640136878242375928109)
                ·
                  refine ⟨22355865051329340890973041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59615640136878242375928109 22355865051329340890973041)
                  ·
                    refine ⟨16766898788497005668229781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22355865051329340890973041 16766898788497005668229781)
                    ·
                      refine ⟨785948380710797140698271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16766898788497005668229781 785948380710797140698271)
                      ·
                        rfl

theorem cell23_1530629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1530629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530629 prefixEnd_1530629 := by exact prefixLift 1530629
  have htrace : WordTrace (prefixWord ++ tailWord_1530629) baseStart_1530629 baseEnd_1530629 := by
    simpa [prefixWord, tailWord_1530629, baseEnd_1530629] using wordTrace_append hprefix tailTrace_1530629
  have hstable : (prefixWord ++ tailWord_1530629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530629).length < 2 ^ (prefixWord ++ tailWord_1530629).sum := by decide
  have hdescent : baseEnd_1530629 < baseStart_1530629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530649 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1530649 : Nat := 118140960795 + 1530649 * 2 ^ 59
def prefixEnd_1530649 : Nat := 4983230072969 + 3 ^ 40 * 1530649 * 2
def baseEnd_1530649 : Nat := 785958650323887062448179

theorem tailTrace_1530649 : CollatzResearch.WordTrace tailWord_1530649 prefixEnd_1530649 785958650323887062448179 := by
  unfold tailWord_1530649
  simp only [CollatzResearch.WordTrace]
  refine ⟨55827355431727561882075001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37218236954485041254716667 55827355431727561882075001)
  ·
    refine ⟨41870516573795671411556251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55827355431727561882075001 41870516573795671411556251)
    ·
      refine ⟨62805774860693507117334377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41870516573795671411556251 62805774860693507117334377)
      ·
        refine ⟨47104331145520130338000783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62805774860693507117334377 47104331145520130338000783)
        ·
          refine ⟨70656496718280195507001175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47104331145520130338000783 70656496718280195507001175)
          ·
            refine ⟨105984745077420293260501763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70656496718280195507001175 105984745077420293260501763)
            ·
              refine ⟨158977117616130439890752645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105984745077420293260501763 158977117616130439890752645)
              ·
                refine ⟨29808209553024457479516121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158977117616130439890752645 29808209553024457479516121)
                ·
                  refine ⟨22356157164768343109637091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29808209553024457479516121 22356157164768343109637091)
                  ·
                    refine ⟨33534235747152514664455637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22356157164768343109637091 33534235747152514664455637)
                    ·
                      refine ⟨785958650323887062448179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33534235747152514664455637 785958650323887062448179)
                      ·
                        rfl

theorem cell23_1530649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1530649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530649 prefixEnd_1530649 := by exact prefixLift 1530649
  have htrace : WordTrace (prefixWord ++ tailWord_1530649) baseStart_1530649 baseEnd_1530649 := by
    simpa [prefixWord, tailWord_1530649, baseEnd_1530649] using wordTrace_append hprefix tailTrace_1530649
  have hstable : (prefixWord ++ tailWord_1530649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530649).length < 2 ^ (prefixWord ++ tailWord_1530649).sum := by decide
  have hdescent : baseEnd_1530649 < baseStart_1530649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530660 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 6]
def baseStart_1530660 : Nat := 118140960795 + 1530660 * 2 ^ 59
def prefixEnd_1530660 : Nat := 4983230072969 + 3 ^ 40 * 1530660 * 2
def baseEnd_1530660 : Nat := 87329366512342946601181

theorem tailTrace_1530660 : CollatzResearch.WordTrace tailWord_1530660 prefixEnd_1530660 87329366512342946601181 := by
  unfold tailWord_1530660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27913878317343855380362717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37218504423125140507150289 27913878317343855380362717)
  ·
    refine ⟨10467704369003945767636019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27913878317343855380362717 10467704369003945767636019)
    ·
      refine ⟨15701556553505918651454029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10467704369003945767636019 15701556553505918651454029)
      ·
        refine ⟨5888083707564719494295261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15701556553505918651454029 5888083707564719494295261)
        ·
          refine ⟨2208031390336769810360723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5888083707564719494295261 2208031390336769810360723)
          ·
            refine ⟨3312047085505154715541085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208031390336769810360723 3312047085505154715541085)
            ·
              refine ⟨1242017657064433018327907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312047085505154715541085 1242017657064433018327907)
              ·
                refine ⟨1863026485596649527491861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242017657064433018327907 1863026485596649527491861)
                ·
                  refine ⟨87329366512342946601181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1863026485596649527491861 87329366512342946601181)
                  ·
                    rfl

theorem cell23_1530660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_1530660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530660 prefixEnd_1530660 := by exact prefixLift 1530660
  have htrace : WordTrace (prefixWord ++ tailWord_1530660) baseStart_1530660 baseEnd_1530660 := by
    simpa [prefixWord, tailWord_1530660, baseEnd_1530660] using wordTrace_append hprefix tailTrace_1530660
  have hstable : (prefixWord ++ tailWord_1530660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530660).length < 2 ^ (prefixWord ++ tailWord_1530660).sum := by decide
  have hdescent : baseEnd_1530660 < baseStart_1530660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530673 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_1530673 : Nat := 118140960795 + 1530673 * 2 ^ 59
def prefixEnd_1530673 : Nat := 4983230072969 + 3 ^ 40 * 1530673 * 2
def baseEnd_1530673 : Nat := 261990324619864989516023

theorem tailTrace_1530673 : CollatzResearch.WordTrace tailWord_1530673 prefixEnd_1530673 261990324619864989516023 := by
  unfold tailWord_1530673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55828230783640613980948673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37218820522427075987299115 55828230783640613980948673)
  ·
    refine ⟨41871173087730460485711505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55828230783640613980948673 41871173087730460485711505)
    ·
      refine ⟨31403379815797845364283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41871173087730460485711505 31403379815797845364283629)
      ·
        refine ⟨11776267430924192011606361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31403379815797845364283629 11776267430924192011606361)
        ·
          refine ⟨8832200573193144008704771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11776267430924192011606361 8832200573193144008704771)
          ·
            refine ⟨13248300859789716013057157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832200573193144008704771 13248300859789716013057157)
            ·
              refine ⟨2484056411210571752448217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13248300859789716013057157 2484056411210571752448217)
              ·
                refine ⟨1863042308407928814336163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484056411210571752448217 1863042308407928814336163)
                ·
                  refine ⟨2794563462611893221504245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863042308407928814336163 2794563462611893221504245)
                  ·
                    refine ⟨261990324619864989516023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2794563462611893221504245 261990324619864989516023)
                    ·
                      rfl

theorem cell23_1530673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_1530673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530673 prefixEnd_1530673 := by exact prefixLift 1530673
  have htrace : WordTrace (prefixWord ++ tailWord_1530673) baseStart_1530673 baseEnd_1530673 := by
    simpa [prefixWord, tailWord_1530673, baseEnd_1530673] using wordTrace_append hprefix tailTrace_1530673
  have hstable : (prefixWord ++ tailWord_1530673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530673).length < 2 ^ (prefixWord ++ tailWord_1530673).sum := by decide
  have hdescent : baseEnd_1530673 < baseStart_1530673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530687 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 1, 1, 3]
def baseStart_1530687 : Nat := 118140960795 + 1530687 * 2 ^ 59
def prefixEnd_1530687 : Nat := 4983230072969 + 3 ^ 40 * 1530687 * 2
def baseEnd_1530687 : Nat := 785978162588757913773005

theorem tailTrace_1530687 : CollatzResearch.WordTrace tailWord_1530687 prefixEnd_1530687 785978162588757913773005 := by
  unfold tailWord_1530687
  simp only [CollatzResearch.WordTrace]
  refine ⟨55828741405589894371958315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37219160937059929581305543 55828741405589894371958315)
  ·
    refine ⟨83743112108384841557937473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55828741405589894371958315 83743112108384841557937473)
    ·
      refine ⟨62807334081288631168453105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83743112108384841557937473 62807334081288631168453105)
      ·
        refine ⟨47105500560966473376339829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62807334081288631168453105 47105500560966473376339829)
        ·
          refine ⟨4416140677590606879031859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47105500560966473376339829 4416140677590606879031859)
          ·
            refine ⟨6624211016385910318547789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416140677590606879031859 6624211016385910318547789)
            ·
              refine ⟨2484079131144716369455421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6624211016385910318547789 2484079131144716369455421)
              ·
                refine ⟨931529674179268638545783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2484079131144716369455421 931529674179268638545783)
                ·
                  refine ⟨1397294511268902957818675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931529674179268638545783 1397294511268902957818675)
                  ·
                    refine ⟨2095941766903354436728013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1397294511268902957818675 2095941766903354436728013)
                    ·
                      refine ⟨785978162588757913773005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2095941766903354436728013 785978162588757913773005)
                      ·
                        rfl

theorem cell23_1530687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_1530687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530687 prefixEnd_1530687 := by exact prefixLift 1530687
  have htrace : WordTrace (prefixWord ++ tailWord_1530687) baseStart_1530687 baseEnd_1530687 := by
    simpa [prefixWord, tailWord_1530687, baseEnd_1530687] using wordTrace_append hprefix tailTrace_1530687
  have hstable : (prefixWord ++ tailWord_1530687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530687).length < 2 ^ (prefixWord ++ tailWord_1530687).sum := by decide
  have hdescent : baseEnd_1530687 < baseStart_1530687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530706 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1530706 : Nat := 118140960795 + 1530706 * 2 ^ 59
def prefixEnd_1530706 : Nat := 4983230072969 + 3 ^ 40 * 1530706 * 2
def baseEnd_1530706 : Nat := 785987918721193339435417

theorem tailTrace_1530706 : CollatzResearch.WordTrace tailWord_1530706 prefixEnd_1530706 785987918721193339435417 := by
  unfold tailWord_1530706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957358598130265154224993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37219622928347373744599981 13957358598130265154224993)
  ·
    refine ⟨10468018948597698865668745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13957358598130265154224993 10468018948597698865668745)
    ·
      refine ⟨7851014211448274149251559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10468018948597698865668745 7851014211448274149251559)
      ·
        refine ⟨11776521317172411223877339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7851014211448274149251559 11776521317172411223877339)
        ·
          refine ⟨17664781975758616835816009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11776521317172411223877339 17664781975758616835816009)
          ·
            refine ⟨13248586481818962626862007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17664781975758616835816009 13248586481818962626862007)
            ·
              refine ⟨19872879722728443940293011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13248586481818962626862007 19872879722728443940293011)
              ·
                refine ⟨29809319584092665910439517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19872879722728443940293011 29809319584092665910439517)
                ·
                  refine ⟨11178494844034749716414819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29809319584092665910439517 11178494844034749716414819)
                  ·
                    refine ⟨16767742266052124574622229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11178494844034749716414819 16767742266052124574622229)
                    ·
                      refine ⟨785987918721193339435417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16767742266052124574622229 785987918721193339435417)
                      ·
                        rfl

theorem cell23_1530706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1530706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530706 prefixEnd_1530706 := by exact prefixLift 1530706
  have htrace : WordTrace (prefixWord ++ tailWord_1530706) baseStart_1530706 baseEnd_1530706 := by
    simpa [prefixWord, tailWord_1530706, baseEnd_1530706] using wordTrace_append hprefix tailTrace_1530706
  have hstable : (prefixWord ++ tailWord_1530706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530706).length < 2 ^ (prefixWord ++ tailWord_1530706).sum := by decide
  have hdescent : baseEnd_1530706 < baseStart_1530706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530743 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_1530743 : Nat := 118140960795 + 1530743 * 2 ^ 59
def prefixEnd_1530743 : Nat := 4983230072969 + 3 ^ 40 * 1530743 * 2
def baseEnd_1530743 : Nat := 786006917505409694672747

theorem tailTrace_1530743 : CollatzResearch.WordTrace tailWord_1530743 prefixEnd_1530743 786006917505409694672747 := by
  unfold tailWord_1530743
  simp only [CollatzResearch.WordTrace]
  refine ⟨55830783893387015935996883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37220522595591343957331255 55830783893387015935996883)
  ·
    refine ⟨83746175840080523903995325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55830783893387015935996883 83746175840080523903995325)
    ·
      refine ⟨31404815940030196463998247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83746175840080523903995325 31404815940030196463998247)
      ·
        refine ⟨47107223910045294695997371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31404815940030196463998247 47107223910045294695997371)
        ·
          refine ⟨70660835865067942043996057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47107223910045294695997371 70660835865067942043996057)
          ·
            refine ⟨52995626898800956532997043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70660835865067942043996057 52995626898800956532997043)
            ·
              refine ⟨79493440348201434799495565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52995626898800956532997043 79493440348201434799495565)
              ·
                refine ⟨29810040130575538049810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79493440348201434799495565 29810040130575538049810837)
                ·
                  refine ⟨1397345631120728346084883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29810040130575538049810837 1397345631120728346084883)
                  ·
                    refine ⟨2096018446681092519127325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1397345631120728346084883 2096018446681092519127325)
                    ·
                      refine ⟨786006917505409694672747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096018446681092519127325 786006917505409694672747)
                      ·
                        rfl

theorem cell23_1530743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_1530743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530743 prefixEnd_1530743 := by exact prefixLift 1530743
  have htrace : WordTrace (prefixWord ++ tailWord_1530743) baseStart_1530743 baseEnd_1530743 := by
    simpa [prefixWord, tailWord_1530743, baseEnd_1530743] using wordTrace_append hprefix tailTrace_1530743
  have hstable : (prefixWord ++ tailWord_1530743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530743).length < 2 ^ (prefixWord ++ tailWord_1530743).sum := by decide
  have hdescent : baseEnd_1530743 < baseStart_1530743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530750 : List Nat := [4, 2, 3, 1, 3, 10]
def baseStart_1530750 : Nat := 118140960795 + 1530750 * 2 ^ 59
def prefixEnd_1530750 : Nat := 4983230072969 + 3 ^ 40 * 1530750 * 2
def baseEnd_1530750 : Nat := 3234611159958811388005

theorem tailTrace_1530750 : CollatzResearch.WordTrace tailWord_1530750 prefixEnd_1530750 3234611159958811388005 := by
  unfold tailWord_1530750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978879900545207016437713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37220692802907770754334469 6978879900545207016437713)
  ·
    refine ⟨5234159925408905262328285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978879900545207016437713 5234159925408905262328285)
    ·
      refine ⟨1962809972028339473373107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5234159925408905262328285 1962809972028339473373107)
      ·
        refine ⟨2944214958042509210059661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962809972028339473373107 2944214958042509210059661)
        ·
          refine ⟨1104080609265940953772373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2944214958042509210059661 1104080609265940953772373)
          ·
            refine ⟨3234611159958811388005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1104080609265940953772373 3234611159958811388005)
            ·
              rfl

theorem cell23_1530750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 10].length) (baseStart_1530750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530750 prefixEnd_1530750 := by exact prefixLift 1530750
  have htrace : WordTrace (prefixWord ++ tailWord_1530750) baseStart_1530750 baseEnd_1530750 := by
    simpa [prefixWord, tailWord_1530750, baseEnd_1530750] using wordTrace_append hprefix tailTrace_1530750
  have hstable : (prefixWord ++ tailWord_1530750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530750).length < 2 ^ (prefixWord ++ tailWord_1530750).sum := by decide
  have hdescent : baseEnd_1530750 < baseStart_1530750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530761 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 1, 2, 2]
def baseStart_1530761 : Nat := 118140960795 + 1530761 * 2 ^ 59
def prefixEnd_1530761 : Nat := 4983230072969 + 3 ^ 40 * 1530761 * 2
def baseEnd_1530761 : Nat := 786016160157190624247665

theorem tailTrace_1530761 : CollatzResearch.WordTrace tailWord_1530761 prefixEnd_1530761 786016160157190624247665 := by
  unfold tailWord_1530761
  simp only [CollatzResearch.WordTrace]
  refine ⟨55831440407321805010152137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37220960271547870006768091 55831440407321805010152137)
  ·
    refine ⟨41873580305491353757614103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55831440407321805010152137 41873580305491353757614103)
    ·
      refine ⟨62810370458237030636421155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41873580305491353757614103 62810370458237030636421155)
      ·
        refine ⟨94215555687355545954631733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62810370458237030636421155 94215555687355545954631733)
        ·
          refine ⟨8832708345689582433246725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94215555687355545954631733 8832708345689582433246725)
          ·
            refine ⟨1656132814816796706233761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8832708345689582433246725 1656132814816796706233761)
            ·
              refine ⟨1242099611112597529675321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656132814816796706233761 1242099611112597529675321)
              ·
                refine ⟨931574708334448147256491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242099611112597529675321 931574708334448147256491)
                ·
                  refine ⟨1397362062501672220884737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931574708334448147256491 1397362062501672220884737)
                  ·
                    refine ⟨1048021546876254165663553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1397362062501672220884737 1048021546876254165663553)
                    ·
                      refine ⟨786016160157190624247665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048021546876254165663553 786016160157190624247665)
                      ·
                        rfl

theorem cell23_1530761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 2, 2].length) (baseStart_1530761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530761 prefixEnd_1530761 := by exact prefixLift 1530761
  have htrace : WordTrace (prefixWord ++ tailWord_1530761) baseStart_1530761 baseEnd_1530761 := by
    simpa [prefixWord, tailWord_1530761, baseEnd_1530761] using wordTrace_append hprefix tailTrace_1530761
  have hstable : (prefixWord ++ tailWord_1530761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530761).length < 2 ^ (prefixWord ++ tailWord_1530761).sum := by decide
  have hdescent : baseEnd_1530761 < baseStart_1530761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530774 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1530774 : Nat := 118140960795 + 1530774 * 2 ^ 59
def prefixEnd_1530774 : Nat := 4983230072969 + 3 ^ 40 * 1530774 * 2
def baseEnd_1530774 : Nat := 786022835405699073385105

theorem tailTrace_1530774 : CollatzResearch.WordTrace tailWord_1530774 prefixEnd_1530774 786022835405699073385105 := by
  unfold tailWord_1530774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489494659767169264398461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37221276370849805486916917 3489494659767169264398461)
  ·
    refine ⟨1308560497412688474149423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3489494659767169264398461 1308560497412688474149423)
    ·
      refine ⟨1962840746119032711224135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308560497412688474149423 1962840746119032711224135)
      ·
        refine ⟨2944261119178549066836203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962840746119032711224135 2944261119178549066836203)
        ·
          refine ⟨4416391678767823600254305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944261119178549066836203 4416391678767823600254305)
          ·
            refine ⟨3312293759075867700190729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416391678767823600254305 3312293759075867700190729)
            ·
              refine ⟨2484220319306900775143047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312293759075867700190729 2484220319306900775143047)
              ·
                refine ⟨3726330478960351162714571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484220319306900775143047 3726330478960351162714571)
                ·
                  refine ⟨5589495718440526744071857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726330478960351162714571 5589495718440526744071857)
                  ·
                    refine ⟨4192121788830395058053893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589495718440526744071857 4192121788830395058053893)
                    ·
                      refine ⟨786022835405699073385105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4192121788830395058053893 786022835405699073385105)
                      ·
                        rfl

theorem cell23_1530774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1530774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530774 prefixEnd_1530774 := by exact prefixLift 1530774
  have htrace : WordTrace (prefixWord ++ tailWord_1530774) baseStart_1530774 baseEnd_1530774 := by
    simpa [prefixWord, tailWord_1530774, baseEnd_1530774] using wordTrace_append hprefix tailTrace_1530774
  have hstable : (prefixWord ++ tailWord_1530774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530774).length < 2 ^ (prefixWord ++ tailWord_1530774).sum := by decide
  have hdescent : baseEnd_1530774 < baseStart_1530774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530833 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_1530833 : Nat := 118140960795 + 1530833 * 2 ^ 59
def prefixEnd_1530833 : Nat := 4983230072969 + 3 ^ 40 * 1530833 * 2
def baseEnd_1530833 : Nat := 786053130764314342547333

theorem tailTrace_1530833 : CollatzResearch.WordTrace tailWord_1530833 prefixEnd_1530833 786053130764314342547333 := by
  unfold tailWord_1530833
  simp only [CollatzResearch.WordTrace]
  refine ⟨55834066463060961306773153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37222710975373974204515435 55834066463060961306773153)
  ·
    refine ⟨41875549847295720980079865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55834066463060961306773153 41875549847295720980079865)
    ·
      refine ⟨31406662385471790735059899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41875549847295720980079865 31406662385471790735059899)
      ·
        refine ⟨47109993578207686102589849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31406662385471790735059899 47109993578207686102589849)
        ·
          refine ⟨35332495183655764576942387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47109993578207686102589849 35332495183655764576942387)
          ·
            refine ⟨52998742775483646865413581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35332495183655764576942387 52998742775483646865413581)
            ·
              refine ⟨19874528540806367574530093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52998742775483646865413581 19874528540806367574530093)
              ·
                refine ⟨7452948202802387840448785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19874528540806367574530093 7452948202802387840448785)
                ·
                  refine ⟨5589711152101790880336589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452948202802387840448785 5589711152101790880336589)
                  ·
                    refine ⟨2096141682038171580126221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5589711152101790880336589 2096141682038171580126221)
                    ·
                      refine ⟨786053130764314342547333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096141682038171580126221 786053130764314342547333)
                      ·
                        rfl

theorem cell23_1530833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_1530833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530833 prefixEnd_1530833 := by exact prefixLift 1530833
  have htrace : WordTrace (prefixWord ++ tailWord_1530833) baseStart_1530833 baseEnd_1530833 := by
    simpa [prefixWord, tailWord_1530833, baseEnd_1530833] using wordTrace_append hprefix tailTrace_1530833
  have hstable : (prefixWord ++ tailWord_1530833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530833).length < 2 ^ (prefixWord ++ tailWord_1530833).sum := by decide
  have hdescent : baseEnd_1530833 < baseStart_1530833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530834 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1530834 : Nat := 118140960795 + 1530834 * 2 ^ 59
def prefixEnd_1530834 : Nat := 4983230072969 + 3 ^ 40 * 1530834 * 2
def baseEnd_1530834 : Nat := 786053644244968838634829

theorem tailTrace_1530834 : CollatzResearch.WordTrace tailWord_1530834 prefixEnd_1530834 786053644244968838634829 := by
  unfold tailWord_1530834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13958525734014334619389889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37222735290704892318373037 13958525734014334619389889)
  ·
    refine ⟨10468894300510750964542417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13958525734014334619389889 10468894300510750964542417)
    ·
      refine ⟨7851670725383063223406813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10468894300510750964542417 7851670725383063223406813)
      ·
        refine ⟨2944376522018648708777555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7851670725383063223406813 2944376522018648708777555)
        ·
          refine ⟨4416564783027973063166333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944376522018648708777555 4416564783027973063166333)
          ·
            refine ⟨1656211793635489898687375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4416564783027973063166333 1656211793635489898687375)
            ·
              refine ⟨2484317690453234848031063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656211793635489898687375 2484317690453234848031063)
              ·
                refine ⟨3726476535679852272046595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484317690453234848031063 3726476535679852272046595)
                ·
                  refine ⟨5589714803519778408069893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726476535679852272046595 5589714803519778408069893)
                  ·
                    refine ⟨1048071525659958451513105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589714803519778408069893 1048071525659958451513105)
                    ·
                      refine ⟨786053644244968838634829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048071525659958451513105 786053644244968838634829)
                      ·
                        rfl

theorem cell23_1530834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1530834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530834 prefixEnd_1530834 := by exact prefixLift 1530834
  have htrace : WordTrace (prefixWord ++ tailWord_1530834) baseStart_1530834 baseEnd_1530834 := by
    simpa [prefixWord, tailWord_1530834, baseEnd_1530834] using wordTrace_append hprefix tailTrace_1530834
  have hstable : (prefixWord ++ tailWord_1530834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530834).length < 2 ^ (prefixWord ++ tailWord_1530834).sum := by decide
  have hdescent : baseEnd_1530834 < baseStart_1530834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530870 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1530870 : Nat := 118140960795 + 1530870 * 2 ^ 59
def prefixEnd_1530870 : Nat := 4983230072969 + 3 ^ 40 * 1530870 * 2
def baseEnd_1530870 : Nat := 262024043182843565928221

theorem tailTrace_1530870 : CollatzResearch.WordTrace tailWord_1530870 prefixEnd_1530870 262024043182843565928221 := by
  unfold tailWord_1530870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489713497745432289116879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37223610642617944417246709 3489713497745432289116879)
  ·
    refine ⟨5234570246618148433675319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489713497745432289116879 5234570246618148433675319)
    ·
      refine ⟨7851855369927222650512979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234570246618148433675319 7851855369927222650512979)
      ·
        refine ⟨11777783054890833975769469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7851855369927222650512979 11777783054890833975769469)
        ·
          refine ⟨4416668645584062740913551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11777783054890833975769469 4416668645584062740913551)
          ·
            refine ⟨6625002968376094111370327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416668645584062740913551 6625002968376094111370327)
            ·
              refine ⟨9937504452564141167055491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625002968376094111370327 9937504452564141167055491)
              ·
                refine ⟨14906256678846211750583237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937504452564141167055491 14906256678846211750583237)
                ·
                  refine ⟨2794923127283664703234357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14906256678846211750583237 2794923127283664703234357)
                  ·
                    refine ⟨262024043182843565928221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2794923127283664703234357 262024043182843565928221)
                    ·
                      rfl

theorem cell23_1530870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1530870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530870 prefixEnd_1530870 := by exact prefixLift 1530870
  have htrace : WordTrace (prefixWord ++ tailWord_1530870) baseStart_1530870 baseEnd_1530870 := by
    simpa [prefixWord, tailWord_1530870, baseEnd_1530870] using wordTrace_append hprefix tailTrace_1530870
  have hstable : (prefixWord ++ tailWord_1530870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530870).length < 2 ^ (prefixWord ++ tailWord_1530870).sum := by decide
  have hdescent : baseEnd_1530870 < baseStart_1530870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530917 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1530917 : Nat := 118140960795 + 1530917 * 2 ^ 59
def prefixEnd_1530917 : Nat := 4983230072969 + 3 ^ 40 * 1530917 * 2
def baseEnd_1530917 : Nat := 262032087713097337965649

theorem tailTrace_1530917 : CollatzResearch.WordTrace tailWord_1530917 prefixEnd_1530917 262032087713097337965649 := by
  unfold tailWord_1530917
  simp only [CollatzResearch.WordTrace]
  refine ⟨55837130194756643652831005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37224753463171095768554003 55837130194756643652831005)
  ·
    refine ⟨20938923823033741369811627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55837130194756643652831005 20938923823033741369811627)
    ·
      refine ⟨31408385734550612054717441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20938923823033741369811627 31408385734550612054717441)
      ·
        refine ⟨23556289300912959041038081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31408385734550612054717441 23556289300912959041038081)
        ·
          refine ⟨17667216975684719280778561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23556289300912959041038081 17667216975684719280778561)
          ·
            refine ⟨13250412731763539460583921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17667216975684719280778561 13250412731763539460583921)
            ·
              refine ⟨9937809548822654595437941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250412731763539460583921 9937809548822654595437941)
              ·
                refine ⟨931669645202123868322307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9937809548822654595437941 931669645202123868322307)
                ·
                  refine ⟨1397504467803185802483461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931669645202123868322307 1397504467803185802483461)
                  ·
                    refine ⟨262032087713097337965649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397504467803185802483461 262032087713097337965649)
                    ·
                      rfl

theorem cell23_1530917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1530917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530917 prefixEnd_1530917 := by exact prefixLift 1530917
  have htrace : WordTrace (prefixWord ++ tailWord_1530917) baseStart_1530917 baseEnd_1530917 := by
    simpa [prefixWord, tailWord_1530917, baseEnd_1530917] using wordTrace_append hprefix tailTrace_1530917
  have hstable : (prefixWord ++ tailWord_1530917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530917).length < 2 ^ (prefixWord ++ tailWord_1530917).sum := by decide
  have hdescent : baseEnd_1530917 < baseStart_1530917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530930 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_1530930 : Nat := 118140960795 + 1530930 * 2 ^ 59
def prefixEnd_1530930 : Nat := 4983230072969 + 3 ^ 40 * 1530930 * 2
def baseEnd_1530930 : Nat := 87344770931977829226043

theorem tailTrace_1530930 : CollatzResearch.WordTrace tailWord_1530930 prefixEnd_1530930 87344770931977829226043 := by
  unfold tailWord_1530930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959401085927386718263561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37225069562473031248702829 13959401085927386718263561)
  ·
    refine ⟨10469550814445540038697671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13959401085927386718263561 10469550814445540038697671)
    ·
      refine ⟨15704326221668310058046507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10469550814445540038697671 15704326221668310058046507)
      ·
        refine ⟨23556489332502465087069761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15704326221668310058046507 23556489332502465087069761)
        ·
          refine ⟨17667366999376848815302321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23556489332502465087069761 17667366999376848815302321)
          ·
            refine ⟨13250525249532636611476741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17667366999376848815302321 13250525249532636611476741)
            ·
              refine ⟨2484473484287369364651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13250525249532636611476741 2484473484287369364651889)
              ·
                refine ⟨1863355113215527023488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484473484287369364651889 1863355113215527023488917)
                ·
                  refine ⟨87344770931977829226043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1863355113215527023488917 87344770931977829226043)
                  ·
                    rfl

theorem cell23_1530930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_1530930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530930 prefixEnd_1530930 := by exact prefixLift 1530930
  have htrace : WordTrace (prefixWord ++ tailWord_1530930) baseStart_1530930 baseEnd_1530930 := by
    simpa [prefixWord, tailWord_1530930, baseEnd_1530930] using wordTrace_append hprefix tailTrace_1530930
  have hstable : (prefixWord ++ tailWord_1530930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530930).length < 2 ^ (prefixWord ++ tailWord_1530930).sum := by decide
  have hdescent : baseEnd_1530930 < baseStart_1530930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530933 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1530933 : Nat := 118140960795 + 1530933 * 2 ^ 59
def prefixEnd_1530933 : Nat := 4983230072969 + 3 ^ 40 * 1530933 * 2
def baseEnd_1530933 : Nat := 786104478829763951296873

theorem tailTrace_1530933 : CollatzResearch.WordTrace tailWord_1530933 prefixEnd_1530933 786104478829763951296873 := by
  unfold tailWord_1530933
  simp only [CollatzResearch.WordTrace]
  refine ⟨55837713762698678385413453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37225142508465785590275635 55837713762698678385413453)
  ·
    refine ⟨20939142661012004394530045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55837713762698678385413453 20939142661012004394530045)
    ·
      refine ⟨7852178497879501647948767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20939142661012004394530045 7852178497879501647948767)
      ·
        refine ⟨11778267746819252471923151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852178497879501647948767 11778267746819252471923151)
        ·
          refine ⟨17667401620228878707884727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778267746819252471923151 17667401620228878707884727)
          ·
            refine ⟨26501102430343318061827091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17667401620228878707884727 26501102430343318061827091)
            ·
              refine ⟨39751653645514977092740637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26501102430343318061827091 39751653645514977092740637)
              ·
                refine ⟨14906870117068116409777739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39751653645514977092740637 14906870117068116409777739)
                ·
                  refine ⟨22360305175602174614666609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14906870117068116409777739 22360305175602174614666609)
                  ·
                    refine ⟨16770228881701630960999957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22360305175602174614666609 16770228881701630960999957)
                    ·
                      refine ⟨786104478829763951296873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16770228881701630960999957 786104478829763951296873)
                      ·
                        rfl

theorem cell23_1530933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1530933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530933 prefixEnd_1530933 := by exact prefixLift 1530933
  have htrace : WordTrace (prefixWord ++ tailWord_1530933) baseStart_1530933 baseEnd_1530933 := by
    simpa [prefixWord, tailWord_1530933, baseEnd_1530933] using wordTrace_append hprefix tailTrace_1530933
  have hstable : (prefixWord ++ tailWord_1530933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530933).length < 2 ^ (prefixWord ++ tailWord_1530933).sum := by decide
  have hdescent : baseEnd_1530933 < baseStart_1530933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530977 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_1530977 : Nat := 118140960795 + 1530977 * 2 ^ 59
def prefixEnd_1530977 : Nat := 4983230072969 + 3 ^ 40 * 1530977 * 2
def baseEnd_1530977 : Nat := 262042357326187259715557

theorem tailTrace_1530977 : CollatzResearch.WordTrace tailWord_1530977 prefixEnd_1530977 262042357326187259715557 := by
  unfold tailWord_1530977
  simp only [CollatzResearch.WordTrace]
  refine ⟨55839318574539273900015185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37226212383026182600010123 55839318574539273900015185)
  ·
    refine ⟨41879488930904455425011389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55839318574539273900015185 41879488930904455425011389)
    ·
      refine ⟨15704808349089170784379271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41879488930904455425011389 15704808349089170784379271)
      ·
        refine ⟨23557212523633756176568907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15704808349089170784379271 23557212523633756176568907)
        ·
          refine ⟨35335818785450634264853361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557212523633756176568907 35335818785450634264853361)
          ·
            refine ⟨26501864089087975698640021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35335818785450634264853361 26501864089087975698640021)
            ·
              refine ⟨1242274879175998860873751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26501864089087975698640021 1242274879175998860873751)
              ·
                refine ⟨1863412318763998291310627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242274879175998860873751 1863412318763998291310627)
                ·
                  refine ⟨2795118478145997436965941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863412318763998291310627 2795118478145997436965941)
                  ·
                    refine ⟨262042357326187259715557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2795118478145997436965941 262042357326187259715557)
                    ·
                      rfl

theorem cell23_1530977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_1530977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1530977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1530977 prefixEnd_1530977 := by exact prefixLift 1530977
  have htrace : WordTrace (prefixWord ++ tailWord_1530977) baseStart_1530977 baseEnd_1530977 := by
    simpa [prefixWord, tailWord_1530977, baseEnd_1530977] using wordTrace_append hprefix tailTrace_1530977
  have hstable : (prefixWord ++ tailWord_1530977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530977).length < 2 ^ (prefixWord ++ tailWord_1530977).sum := by decide
  have hdescent : baseEnd_1530977 < baseStart_1530977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531000 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1531000 : Nat := 118140960795 + 1531000 * 2 ^ 59
def prefixEnd_1531000 : Nat := 4983230072969 + 3 ^ 40 * 1531000 * 2
def baseEnd_1531000 : Nat := 786138882033615189159065

theorem tailTrace_1531000 : CollatzResearch.WordTrace tailWord_1531000 prefixEnd_1531000 786138882033615189159065 := by
  unfold tailWord_1531000
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920078726727974414051227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37226771635637299218734969 27920078726727974414051227)
  ·
    refine ⟨41880118090091961621076841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27920078726727974414051227 41880118090091961621076841)
    ·
      refine ⟨31410088567568971215807631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41880118090091961621076841 31410088567568971215807631)
      ·
        refine ⟨47115132851353456823711447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31410088567568971215807631 47115132851353456823711447)
        ·
          refine ⟨70672699277030185235567171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47115132851353456823711447 70672699277030185235567171)
          ·
            refine ⟨106009048915545277853350757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70672699277030185235567171 106009048915545277853350757)
            ·
              refine ⟨19876696671664739597503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106009048915545277853350757 19876696671664739597503267)
              ·
                refine ⟨29815045007497109396254901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19876696671664739597503267 29815045007497109396254901)
                ·
                  refine ⟨2795160469452854005898897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29815045007497109396254901 2795160469452854005898897)
                  ·
                    refine ⟨2096370352089640504424173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795160469452854005898897 2096370352089640504424173)
                    ·
                      refine ⟨786138882033615189159065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096370352089640504424173 786138882033615189159065)
                      ·
                        rfl

theorem cell23_1531000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1531000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531000 prefixEnd_1531000 := by exact prefixLift 1531000
  have htrace : WordTrace (prefixWord ++ tailWord_1531000) baseStart_1531000 baseEnd_1531000 := by
    simpa [prefixWord, tailWord_1531000, baseEnd_1531000] using wordTrace_append hprefix tailTrace_1531000
  have hstable : (prefixWord ++ tailWord_1531000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531000).length < 2 ^ (prefixWord ++ tailWord_1531000).sum := by decide
  have hdescent : baseEnd_1531000 < baseStart_1531000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531017 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_1531017 : Nat := 118140960795 + 1531017 * 2 ^ 59
def prefixEnd_1531017 : Nat := 4983230072969 + 3 ^ 40 * 1531017 * 2
def baseEnd_1531017 : Nat := 786147611204741622646487

theorem tailTrace_1531017 : CollatzResearch.WordTrace tailWord_1531017 prefixEnd_1531017 786147611204741622646487 := by
  unfold tailWord_1531017
  simp only [CollatzResearch.WordTrace]
  refine ⟨55840777494394360731471305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37227184996262907154314203 55840777494394360731471305)
  ·
    refine ⟨41880583120795770548603479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55840777494394360731471305 41880583120795770548603479)
    ·
      refine ⟨62820874681193655822905219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41880583120795770548603479 62820874681193655822905219)
      ·
        refine ⟨94231312021790483734357829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62820874681193655822905219 94231312021790483734357829)
        ·
          refine ⟨17668371004085715700192093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94231312021790483734357829 17668371004085715700192093)
          ·
            refine ⟨6625639126532143387572035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17668371004085715700192093 6625639126532143387572035)
            ·
              refine ⟨9938458689798215081358053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625639126532143387572035 9938458689798215081358053)
              ·
                refine ⟨1863461004337165327754635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9938458689798215081358053 1863461004337165327754635)
                ·
                  refine ⟨2795191506505747991631953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863461004337165327754635 2795191506505747991631953)
                  ·
                    refine ⟨2096393629879310993723965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795191506505747991631953 2096393629879310993723965)
                    ·
                      refine ⟨786147611204741622646487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096393629879310993723965 786147611204741622646487)
                      ·
                        rfl

theorem cell23_1531017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_1531017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531017 prefixEnd_1531017 := by exact prefixLift 1531017
  have htrace : WordTrace (prefixWord ++ tailWord_1531017) baseStart_1531017 baseEnd_1531017 := by
    simpa [prefixWord, tailWord_1531017, baseEnd_1531017] using wordTrace_append hprefix tailTrace_1531017
  have hstable : (prefixWord ++ tailWord_1531017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531017).length < 2 ^ (prefixWord ++ tailWord_1531017).sum := by decide
  have hdescent : baseEnd_1531017 < baseStart_1531017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531033 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_1531033 : Nat := 118140960795 + 1531033 * 2 ^ 59
def prefixEnd_1531033 : Nat := 4983230072969 + 3 ^ 40 * 1531033 * 2
def baseEnd_1531033 : Nat := 262051942298404520015471

theorem tailTrace_1531033 : CollatzResearch.WordTrace tailWord_1531033 prefixEnd_1531033 262051942298404520015471 := by
  unfold tailWord_1531033
  simp only [CollatzResearch.WordTrace]
  refine ⟨55841361062336395464053753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37227574041557596976035835 55841361062336395464053753)
  ·
    refine ⟨41881020796752296598040315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55841361062336395464053753 41881020796752296598040315)
    ·
      refine ⟨62821531195128444897060473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41881020796752296598040315 62821531195128444897060473)
      ·
        refine ⟨47116148396346333672795355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62821531195128444897060473 47116148396346333672795355)
        ·
          refine ⟨70674222594519500509193033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47116148396346333672795355 70674222594519500509193033)
          ·
            refine ⟨53005666945889625381894775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70674222594519500509193033 53005666945889625381894775)
            ·
              refine ⟨79508500418834438072842163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53005666945889625381894775 79508500418834438072842163)
              ·
                refine ⟨119262750628251657109263245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79508500418834438072842163 119262750628251657109263245)
                ·
                  refine ⟨44723531485594371415973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119262750628251657109263245 44723531485594371415973717)
                  ·
                    refine ⟨262051942298404520015471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44723531485594371415973717 262051942298404520015471)
                    ·
                      rfl

theorem cell23_1531033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_1531033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531033 prefixEnd_1531033 := by exact prefixLift 1531033
  have htrace : WordTrace (prefixWord ++ tailWord_1531033) baseStart_1531033 baseEnd_1531033 := by
    simpa [prefixWord, tailWord_1531033, baseEnd_1531033] using wordTrace_append hprefix tailTrace_1531033
  have hstable : (prefixWord ++ tailWord_1531033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531033).length < 2 ^ (prefixWord ++ tailWord_1531033).sum := by decide
  have hdescent : baseEnd_1531033 < baseStart_1531033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531034 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1531034 : Nat := 118140960795 + 1531034 * 2 ^ 59
def prefixEnd_1531034 : Nat := 4983230072969 + 3 ^ 40 * 1531034 * 2
def baseEnd_1531034 : Nat := 786156340375868056133909

theorem tailTrace_1531034 : CollatzResearch.WordTrace tailWord_1531034 prefixEnd_1531034 786156340375868056133909 := by
  unfold tailWord_1531034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960349383833193158710039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37227598356888515089893437 13960349383833193158710039)
  ·
    refine ⟨20940524075749789738065059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13960349383833193158710039 20940524075749789738065059)
    ·
      refine ⟨31410786113624684607097589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20940524075749789738065059 31410786113624684607097589)
      ·
        refine ⟨2944761198152314181915399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31410786113624684607097589 2944761198152314181915399)
        ·
          refine ⟨4417141797228471272873099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944761198152314181915399 4417141797228471272873099)
          ·
            refine ⟨6625712695842706909309649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417141797228471272873099 6625712695842706909309649)
            ·
              refine ⟨4969284521882030181982237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625712695842706909309649 4969284521882030181982237)
              ·
                refine ⟨1863481695705761318243339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4969284521882030181982237 1863481695705761318243339)
                ·
                  refine ⟨2795222543558641977365009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863481695705761318243339 2795222543558641977365009)
                  ·
                    refine ⟨2096416907668981483023757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795222543558641977365009 2096416907668981483023757)
                    ·
                      refine ⟨786156340375868056133909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096416907668981483023757 786156340375868056133909)
                      ·
                        rfl

theorem cell23_1531034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1531034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531034 prefixEnd_1531034 := by exact prefixLift 1531034
  have htrace : WordTrace (prefixWord ++ tailWord_1531034) baseStart_1531034 baseEnd_1531034 := by
    simpa [prefixWord, tailWord_1531034, baseEnd_1531034] using wordTrace_append hprefix tailTrace_1531034
  have hstable : (prefixWord ++ tailWord_1531034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531034).length < 2 ^ (prefixWord ++ tailWord_1531034).sum := by decide
  have hdescent : baseEnd_1531034 < baseStart_1531034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531078 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1531078 : Nat := 118140960795 + 1531078 * 2 ^ 59
def prefixEnd_1531078 : Nat := 4983230072969 + 3 ^ 40 * 1531078 * 2
def baseEnd_1531078 : Nat := 786178933524665883983707

theorem tailTrace_1531078 : CollatzResearch.WordTrace tailWord_1531078 prefixEnd_1531078 786178933524665883983707 := by
  unfold tailWord_1531078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745093823349167754670059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37228668231448912099627925 1745093823349167754670059)
  ·
    refine ⟨2617640735023751632005089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745093823349167754670059 2617640735023751632005089)
    ·
      refine ⟨1963230551267813724003817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2617640735023751632005089 1963230551267813724003817)
      ·
        refine ⟨1472422913450860293002863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963230551267813724003817 1472422913450860293002863)
        ·
          refine ⟨2208634370176290439504295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472422913450860293002863 2208634370176290439504295)
          ·
            refine ⟨3312951555264435659256443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208634370176290439504295 3312951555264435659256443)
            ·
              refine ⟨4969427332896653488884665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312951555264435659256443 4969427332896653488884665)
              ·
                refine ⟨3727070499672490116663499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4969427332896653488884665 3727070499672490116663499)
                ·
                  refine ⟨5590605749508735174995249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727070499672490116663499 5590605749508735174995249)
                  ·
                    refine ⟨4192954312131551381246437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590605749508735174995249 4192954312131551381246437)
                    ·
                      refine ⟨786178933524665883983707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4192954312131551381246437 786178933524665883983707)
                      ·
                        rfl

theorem cell23_1531078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1531078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531078 prefixEnd_1531078 := by exact prefixLift 1531078
  have htrace : WordTrace (prefixWord ++ tailWord_1531078) baseStart_1531078 baseEnd_1531078 := by
    simpa [prefixWord, tailWord_1531078, baseEnd_1531078] using wordTrace_append hprefix tailTrace_1531078
  have hstable : (prefixWord ++ tailWord_1531078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531078).length < 2 ^ (prefixWord ++ tailWord_1531078).sum := by decide
  have hdescent : baseEnd_1531078 < baseStart_1531078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531085 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1531085 : Nat := 118140960795 + 1531085 * 2 ^ 59
def prefixEnd_1531085 : Nat := 4983230072969 + 3 ^ 40 * 1531085 * 2
def baseEnd_1531085 : Nat := 786182527889247356596175

theorem tailTrace_1531085 : CollatzResearch.WordTrace tailWord_1531085 prefixEnd_1531085 786182527889247356596175 := by
  unfold tailWord_1531085
  simp only [CollatzResearch.WordTrace]
  refine ⟨55843257658148008344946709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37228838438765338896631139 55843257658148008344946709)
  ·
    refine ⟨2617652702725687891169377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55843257658148008344946709 2617652702725687891169377)
    ·
      refine ⟨1963239527044265918377033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2617652702725687891169377 1963239527044265918377033)
      ·
        refine ⟨1472429645283199438782775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963239527044265918377033 1472429645283199438782775)
        ·
          refine ⟨2208644467924799158174163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472429645283199438782775 2208644467924799158174163)
          ·
            refine ⟨3312966701887198737261245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208644467924799158174163 3312966701887198737261245)
            ·
              refine ⟨1242362513207699526472967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312966701887198737261245 1242362513207699526472967)
              ·
                refine ⟨1863543769811549289709451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242362513207699526472967 1863543769811549289709451)
                ·
                  refine ⟨2795315654717323934564177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863543769811549289709451 2795315654717323934564177)
                  ·
                    refine ⟨2096486741037992950923133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795315654717323934564177 2096486741037992950923133)
                    ·
                      refine ⟨786182527889247356596175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096486741037992950923133 786182527889247356596175)
                      ·
                        rfl

theorem cell23_1531085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1531085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531085 prefixEnd_1531085 := by exact prefixLift 1531085
  have htrace : WordTrace (prefixWord ++ tailWord_1531085) baseStart_1531085 baseEnd_1531085 := by
    simpa [prefixWord, tailWord_1531085, baseEnd_1531085] using wordTrace_append hprefix tailTrace_1531085
  have hstable : (prefixWord ++ tailWord_1531085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531085).length < 2 ^ (prefixWord ++ tailWord_1531085).sum := by decide
  have hdescent : baseEnd_1531085 < baseStart_1531085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531117 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1531117 : Nat := 118140960795 + 1531117 * 2 ^ 59
def prefixEnd_1531117 : Nat := 4983230072969 + 3 ^ 40 * 1531117 * 2
def baseEnd_1531117 : Nat := 786198959270191231396027

theorem tailTrace_1531117 : CollatzResearch.WordTrace tailWord_1531117 prefixEnd_1531117 786198959270191231396027 := by
  unfold tailWord_1531117
  simp only [CollatzResearch.WordTrace]
  refine ⟨55844424794032077810111605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37229616529354718540074403 55844424794032077810111605)
  ·
    refine ⟨5235414824440507294697963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55844424794032077810111605 5235414824440507294697963)
    ·
      refine ⟨7853122236660760942046945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235414824440507294697963 7853122236660760942046945)
      ·
        refine ⟨5889841677495570706535209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7853122236660760942046945 5889841677495570706535209)
        ·
          refine ⟨4417381258121678029901407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5889841677495570706535209 4417381258121678029901407)
          ·
            refine ⟨6626071887182517044852111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417381258121678029901407 6626071887182517044852111)
            ·
              refine ⟨9939107830773775567278167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626071887182517044852111 9939107830773775567278167)
              ·
                refine ⟨14908661746160663350917251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9939107830773775567278167 14908661746160663350917251)
                ·
                  refine ⟨22362992619240995026375877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14908661746160663350917251 22362992619240995026375877)
                  ·
                    refine ⟨4193061116107686567445477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22362992619240995026375877 4193061116107686567445477)
                    ·
                      refine ⟨786198959270191231396027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4193061116107686567445477 786198959270191231396027)
                      ·
                        rfl

theorem cell23_1531117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1531117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531117 prefixEnd_1531117 := by exact prefixLift 1531117
  have htrace : WordTrace (prefixWord ++ tailWord_1531117) baseStart_1531117 baseEnd_1531117 := by
    simpa [prefixWord, tailWord_1531117, baseEnd_1531117] using wordTrace_append hprefix tailTrace_1531117
  have hstable : (prefixWord ++ tailWord_1531117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531117).length < 2 ^ (prefixWord ++ tailWord_1531117).sum := by decide
  have hdescent : baseEnd_1531117 < baseStart_1531117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531177 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 6, 2]
def baseStart_1531177 : Nat := 118140960795 + 1531177 * 2 ^ 59
def prefixEnd_1531177 : Nat := 4983230072969 + 3 ^ 40 * 1531177 * 2
def baseEnd_1531177 : Nat := 786229768109460996645751

theorem tailTrace_1531177 : CollatzResearch.WordTrace tailWord_1531177 prefixEnd_1531177 786229768109460996645751 := by
  unfold tailWord_1531177
  simp only [CollatzResearch.WordTrace]
  refine ⟨55846613173814708057295785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37231075449209805371530523 55846613173814708057295785)
  ·
    refine ⟨41884959880361031042971839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55846613173814708057295785 41884959880361031042971839)
    ·
      refine ⟨62827439820541546564457759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41884959880361031042971839 62827439820541546564457759)
      ·
        refine ⟨94241159730812319846686639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62827439820541546564457759 94241159730812319846686639)
        ·
          refine ⟨141361739596218479770029959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94241159730812319846686639 141361739596218479770029959)
          ·
            refine ⟨212042609394327719655044939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141361739596218479770029959 212042609394327719655044939)
            ·
              refine ⟨318063914091491579482567409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212042609394327719655044939 318063914091491579482567409)
              ·
                refine ⟨238547935568618684611925557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318063914091491579482567409 238547935568618684611925557)
                ·
                  refine ⟨22363868959558001682368021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238547935568618684611925557 22363868959558001682368021)
                  ·
                    refine ⟨1048306357479281328861001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22363868959558001682368021 1048306357479281328861001)
                    ·
                      refine ⟨786229768109460996645751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048306357479281328861001 786229768109460996645751)
                      ·
                        rfl

theorem cell23_1531177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6, 2].length) (baseStart_1531177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531177 prefixEnd_1531177 := by exact prefixLift 1531177
  have htrace : WordTrace (prefixWord ++ tailWord_1531177) baseStart_1531177 baseEnd_1531177 := by
    simpa [prefixWord, tailWord_1531177, baseEnd_1531177] using wordTrace_append hprefix tailTrace_1531177
  have hstable : (prefixWord ++ tailWord_1531177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531177).length < 2 ^ (prefixWord ++ tailWord_1531177).sum := by decide
  have hdescent : baseEnd_1531177 < baseStart_1531177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531200 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 10]
def baseStart_1531200 : Nat := 118140960795 + 1531200 * 2 ^ 59
def prefixEnd_1531200 : Nat := 4983230072969 + 3 ^ 40 * 1531200 * 2
def baseEnd_1531200 : Nat := 87360175351612711850905

theorem tailTrace_1531200 : CollatzResearch.WordTrace tailWord_1531200 prefixEnd_1531200 87360175351612711850905 := by
  unfold tailWord_1531200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27923726026365691492691527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37231634701820921990255369 27923726026365691492691527)
  ·
    refine ⟨41885589039548537239037291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27923726026365691492691527 41885589039548537239037291)
    ·
      refine ⟨62828383559322805858555937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41885589039548537239037291 62828383559322805858555937)
      ·
        refine ⟨47121287669492104393916953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62828383559322805858555937 47121287669492104393916953)
        ·
          refine ⟨35340965752119078295437715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47121287669492104393916953 35340965752119078295437715)
          ·
            refine ⟨53011448628178617443156573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35340965752119078295437715 53011448628178617443156573)
            ·
              refine ⟨19879293235566981541183715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53011448628178617443156573 19879293235566981541183715)
              ·
                refine ⟨29818939853350472311775573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19879293235566981541183715 29818939853350472311775573)
                ·
                  refine ⟨87360175351612711850905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29818939853350472311775573 87360175351612711850905)
                  ·
                    rfl

theorem cell23_1531200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_1531200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531200 prefixEnd_1531200 := by exact prefixLift 1531200
  have htrace : WordTrace (prefixWord ++ tailWord_1531200) baseStart_1531200 baseEnd_1531200 := by
    simpa [prefixWord, tailWord_1531200, baseEnd_1531200] using wordTrace_append hprefix tailTrace_1531200
  have hstable : (prefixWord ++ tailWord_1531200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531200).length < 2 ^ (prefixWord ++ tailWord_1531200).sum := by decide
  have hdescent : baseEnd_1531200 < baseStart_1531200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531214 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1531214 : Nat := 118140960795 + 1531214 * 2 ^ 59
def prefixEnd_1531214 : Nat := 4983230072969 + 3 ^ 40 * 1531214 * 2
def baseEnd_1531214 : Nat := 786248766893677351883081

theorem tailTrace_1531214 : CollatzResearch.WordTrace tailWord_1531214 prefixEnd_1531214 786248766893677351883081 := by
  unfold tailWord_1531214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980995334335082922049087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37231975116453775584261797 6980995334335082922049087)
  ·
    refine ⟨10471493001502624383073631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6980995334335082922049087 10471493001502624383073631)
    ·
      refine ⟨15707239502253936574610447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10471493001502624383073631 15707239502253936574610447)
      ·
        refine ⟨23560859253380904861915671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15707239502253936574610447 23560859253380904861915671)
        ·
          refine ⟨35341288880071357292873507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23560859253380904861915671 35341288880071357292873507)
          ·
            refine ⟨53011933320107035939310261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35341288880071357292873507 53011933320107035939310261)
            ·
              refine ⟨4969868748760034619310337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53011933320107035939310261 4969868748760034619310337)
              ·
                refine ⟨3727401561570025964482753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4969868748760034619310337 3727401561570025964482753)
                ·
                  refine ⟨2795551171177519473362065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3727401561570025964482753 2795551171177519473362065)
                  ·
                    refine ⟨2096663378383139605021549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795551171177519473362065 2096663378383139605021549)
                    ·
                      refine ⟨786248766893677351883081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096663378383139605021549 786248766893677351883081)
                      ·
                        rfl

theorem cell23_1531214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1531214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531214 prefixEnd_1531214 := by exact prefixLift 1531214
  have htrace : WordTrace (prefixWord ++ tailWord_1531214) baseStart_1531214 baseEnd_1531214 := by
    simpa [prefixWord, tailWord_1531214, baseEnd_1531214] using wordTrace_append hprefix tailTrace_1531214
  have hstable : (prefixWord ++ tailWord_1531214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531214).length < 2 ^ (prefixWord ++ tailWord_1531214).sum := by decide
  have hdescent : baseEnd_1531214 < baseStart_1531214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531217 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 6]
def baseStart_1531217 : Nat := 118140960795 + 1531217 * 2 ^ 59
def prefixEnd_1531217 : Nat := 4983230072969 + 3 ^ 40 * 1531217 * 2
def baseEnd_1531217 : Nat := 87361145259515648905063

theorem tailTrace_1531217 : CollatzResearch.WordTrace tailWord_1531217 prefixEnd_1531217 87361145259515648905063 := by
  unfold tailWord_1531217
  simp only [CollatzResearch.WordTrace]
  refine ⟨55848072093669794888751905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37232048062446529925834603 55848072093669794888751905)
  ·
    refine ⟨41886054070252346166563929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55848072093669794888751905 41886054070252346166563929)
    ·
      refine ⟨31414540552689259624922947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41886054070252346166563929 31414540552689259624922947)
      ·
        refine ⟨47121810829033889437384421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31414540552689259624922947 47121810829033889437384421)
        ·
          refine ⟨8835339530443854269509579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47121810829033889437384421 8835339530443854269509579)
          ·
            refine ⟨13253009295665781404264369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835339530443854269509579 13253009295665781404264369)
            ·
              refine ⟨9939756971749336053198277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13253009295665781404264369 9939756971749336053198277)
              ·
                refine ⟨1863704432203000509974677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9939756971749336053198277 1863704432203000509974677)
                ·
                  refine ⟨87361145259515648905063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1863704432203000509974677 87361145259515648905063)
                  ·
                    rfl

theorem cell23_1531217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_1531217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531217 prefixEnd_1531217 := by exact prefixLift 1531217
  have htrace : WordTrace (prefixWord ++ tailWord_1531217) baseStart_1531217 baseEnd_1531217 := by
    simpa [prefixWord, tailWord_1531217, baseEnd_1531217] using wordTrace_append hprefix tailTrace_1531217
  have hstable : (prefixWord ++ tailWord_1531217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531217).length < 2 ^ (prefixWord ++ tailWord_1531217).sum := by decide
  have hdescent : baseEnd_1531217 < baseStart_1531217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531221 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1531221 : Nat := 118140960795 + 1531221 * 2 ^ 59
def prefixEnd_1531221 : Nat := 4983230072969 + 3 ^ 40 * 1531221 * 2
def baseEnd_1531221 : Nat := 262084120419419608165183

theorem tailTrace_1531221 : CollatzResearch.WordTrace tailWord_1531221 prefixEnd_1531221 262084120419419608165183 := by
  unfold tailWord_1531221
  simp only [CollatzResearch.WordTrace]
  refine ⟨55848217985655303571897517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37232145323770202381265011 55848217985655303571897517)
  ·
    refine ⟨20943081744620738839461569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55848217985655303571897517 20943081744620738839461569)
    ·
      refine ⟨15707311308465554129596177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20943081744620738839461569 15707311308465554129596177)
      ·
        refine ⟨11780483481349165597197133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15707311308465554129596177 11780483481349165597197133)
        ·
          refine ⟨4417681305505937098948925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11780483481349165597197133 4417681305505937098948925)
          ·
            refine ⟨1656630489564726412105847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4417681305505937098948925 1656630489564726412105847)
            ·
              refine ⟨2484945734347089618158771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656630489564726412105847 2484945734347089618158771)
              ·
                refine ⟨3727418601520634427238157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484945734347089618158771 3727418601520634427238157)
                ·
                  refine ⟨1397781975570237910214309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3727418601520634427238157 1397781975570237910214309)
                  ·
                    refine ⟨262084120419419608165183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397781975570237910214309 262084120419419608165183)
                    ·
                      rfl

theorem cell23_1531221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1531221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531221 prefixEnd_1531221 := by exact prefixLift 1531221
  have htrace : WordTrace (prefixWord ++ tailWord_1531221) baseStart_1531221 baseEnd_1531221 := by
    simpa [prefixWord, tailWord_1531221, baseEnd_1531221] using wordTrace_append hprefix tailTrace_1531221
  have hstable : (prefixWord ++ tailWord_1531221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531221).length < 2 ^ (prefixWord ++ tailWord_1531221).sum := by decide
  have hdescent : baseEnd_1531221 < baseStart_1531221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531234 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1531234 : Nat := 118140960795 + 1531234 * 2 ^ 59
def prefixEnd_1531234 : Nat := 4983230072969 + 3 ^ 40 * 1531234 * 2
def baseEnd_1531234 : Nat := 87362115167418585959221

theorem tailTrace_1531234 : CollatzResearch.WordTrace tailWord_1531234 prefixEnd_1531234 87362115167418585959221 := by
  unfold tailWord_1531234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13962173033652051698030189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37232461423072137861413837 13962173033652051698030189)
  ·
    refine ⟨5235814887619519386761321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13962173033652051698030189 5235814887619519386761321)
    ·
      refine ⟨3926861165714639540070991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5235814887619519386761321 3926861165714639540070991)
      ·
        refine ⟨5890291748571959310106487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926861165714639540070991 5890291748571959310106487)
        ·
          refine ⟨8835437622857938965159731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890291748571959310106487 8835437622857938965159731)
          ·
            refine ⟨13253156434286908447739597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835437622857938965159731 13253156434286908447739597)
            ·
              refine ⟨4969933662857590667902349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13253156434286908447739597 4969933662857590667902349)
              ·
                refine ⟨1863725123571596500463381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4969933662857590667902349 1863725123571596500463381)
                ·
                  refine ⟨87362115167418585959221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1863725123571596500463381 87362115167418585959221)
                  ·
                    rfl

theorem cell23_1531234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1531234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531234 prefixEnd_1531234 := by exact prefixLift 1531234
  have htrace : WordTrace (prefixWord ++ tailWord_1531234) baseStart_1531234 baseEnd_1531234 := by
    simpa [prefixWord, tailWord_1531234, baseEnd_1531234] using wordTrace_append hprefix tailTrace_1531234
  have hstable : (prefixWord ++ tailWord_1531234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531234).length < 2 ^ (prefixWord ++ tailWord_1531234).sum := by decide
  have hdescent : baseEnd_1531234 < baseStart_1531234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531247 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 3, 5]
def baseStart_1531247 : Nat := 118140960795 + 1531247 * 2 ^ 59
def prefixEnd_1531247 : Nat := 4983230072969 + 3 ^ 40 * 1531247 * 2
def baseEnd_1531247 : Nat := 262088570585091907590143

theorem tailTrace_1531247 : CollatzResearch.WordTrace tailWord_1531247 prefixEnd_1531247 262088570585091907590143 := by
  unfold tailWord_1531247
  simp only [CollatzResearch.WordTrace]
  refine ⟨55849166283561110012343995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37232777522374073341562663 55849166283561110012343995)
  ·
    refine ⟨83773749425341665018515993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55849166283561110012343995 83773749425341665018515993)
    ·
      refine ⟨62830312069006248763886995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83773749425341665018515993 62830312069006248763886995)
      ·
        refine ⟨94245468103509373145830493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62830312069006248763886995 94245468103509373145830493)
        ·
          refine ⟨35342050538816014929686435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94245468103509373145830493 35342050538816014929686435)
          ·
            refine ⟨53013075808224022394529653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35342050538816014929686435 53013075808224022394529653)
            ·
              refine ⟨4969975857021002099487155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53013075808224022394529653 4969975857021002099487155)
              ·
                refine ⟨7454963785531503149230733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969975857021002099487155 7454963785531503149230733)
                ·
                  refine ⟨2795611419574313680961525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7454963785531503149230733 2795611419574313680961525)
                  ·
                    refine ⟨262088570585091907590143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2795611419574313680961525 262088570585091907590143)
                    ·
                      rfl

theorem cell23_1531247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_1531247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531247 prefixEnd_1531247 := by exact prefixLift 1531247
  have htrace : WordTrace (prefixWord ++ tailWord_1531247) baseStart_1531247 baseEnd_1531247 := by
    simpa [prefixWord, tailWord_1531247, baseEnd_1531247] using wordTrace_append hprefix tailTrace_1531247
  have hstable : (prefixWord ++ tailWord_1531247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531247).length < 2 ^ (prefixWord ++ tailWord_1531247).sum := by decide
  have hdescent : baseEnd_1531247 < baseStart_1531247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531271 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_1531271 : Nat := 118140960795 + 1531271 * 2 ^ 59
def prefixEnd_1531271 : Nat := 4983230072969 + 3 ^ 40 * 1531271 * 2
def baseEnd_1531271 : Nat := 786278035290983628870319

theorem tailTrace_1531271 : CollatzResearch.WordTrace tailWord_1531271 prefixEnd_1531271 786278035290983628870319 := by
  unfold tailWord_1531271
  simp only [CollatzResearch.WordTrace]
  refine ⟨55850041635474162111217667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37233361090316108074145111 55850041635474162111217667)
  ·
    refine ⟨83775062453211243166826501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55850041635474162111217667 83775062453211243166826501)
    ·
      refine ⟨15707824209977108093779969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83775062453211243166826501 15707824209977108093779969)
      ·
        refine ⟨11780868157482831070334977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15707824209977108093779969 11780868157482831070334977)
        ·
          refine ⟨8835651118112123302751233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780868157482831070334977 8835651118112123302751233)
          ·
            refine ⟨6626738338584092477063425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835651118112123302751233 6626738338584092477063425)
            ·
              refine ⟨4970053753938069357797569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626738338584092477063425 4970053753938069357797569)
              ·
                refine ⟨3727540315453552018348177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970053753938069357797569 3727540315453552018348177)
                ·
                  refine ⟨2795655236590164013761133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3727540315453552018348177 2795655236590164013761133)
                  ·
                    refine ⟨1048370713721311505160425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2795655236590164013761133 1048370713721311505160425)
                    ·
                      refine ⟨786278035290983628870319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048370713721311505160425 786278035290983628870319)
                      ·
                        rfl

theorem cell23_1531271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_1531271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531271 prefixEnd_1531271 := by exact prefixLift 1531271
  have htrace : WordTrace (prefixWord ++ tailWord_1531271) baseStart_1531271 baseEnd_1531271 := by
    simpa [prefixWord, tailWord_1531271, baseEnd_1531271] using wordTrace_append hprefix tailTrace_1531271
  have hstable : (prefixWord ++ tailWord_1531271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531271).length < 2 ^ (prefixWord ++ tailWord_1531271).sum := by decide
  have hdescent : baseEnd_1531271 < baseStart_1531271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1531287 : Nat := 118140960795 + 1531287 * 2 ^ 59
def prefixEnd_1531287 : Nat := 4983230072969 + 3 ^ 40 * 1531287 * 2
def baseEnd_1531287 : Nat := 786286250981455566270245

theorem tailTrace_1531287 : CollatzResearch.WordTrace tailWord_1531287 prefixEnd_1531287 786286250981455566270245 := by
  unfold tailWord_1531287
  simp only [CollatzResearch.WordTrace]
  refine ⟨55850625203416196843800115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37233750135610797895866743 55850625203416196843800115)
  ·
    refine ⟨83775937805124295265700173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55850625203416196843800115 83775937805124295265700173)
    ·
      refine ⟨31415976676921610724637565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83775937805124295265700173 31415976676921610724637565)
      ·
        refine ⟨11780991253845604021739087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31415976676921610724637565 11780991253845604021739087)
        ·
          refine ⟨17671486880768406032608631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11780991253845604021739087 17671486880768406032608631)
          ·
            refine ⟨26507230321152609048912947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17671486880768406032608631 26507230321152609048912947)
            ·
              refine ⟨39760845481728913573369421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26507230321152609048912947 39760845481728913573369421)
              ·
                refine ⟨14910317055648342590013533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39760845481728913573369421 14910317055648342590013533)
                ·
                  refine ⟨5591368895868128471255075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14910317055648342590013533 5591368895868128471255075)
                  ·
                    refine ⟨8387053343802192706882613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591368895868128471255075 8387053343802192706882613)
                    ·
                      refine ⟨786286250981455566270245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8387053343802192706882613 786286250981455566270245)
                      ·
                        rfl

theorem cell23_1531287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1531287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531287 prefixEnd_1531287 := by exact prefixLift 1531287
  have htrace : WordTrace (prefixWord ++ tailWord_1531287) baseStart_1531287 baseEnd_1531287 := by
    simpa [prefixWord, tailWord_1531287, baseEnd_1531287] using wordTrace_append hprefix tailTrace_1531287
  have hstable : (prefixWord ++ tailWord_1531287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531287).length < 2 ^ (prefixWord ++ tailWord_1531287).sum := by decide
  have hdescent : baseEnd_1531287 < baseStart_1531287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531324 : List Nat := [2, 2, 2, 4, 2, 1, 10]
def baseStart_1531324 : Nat := 118140960795 + 1531324 * 2 ^ 59
def prefixEnd_1531324 : Nat := 4983230072969 + 3 ^ 40 * 1531324 * 2
def baseEnd_1531324 : Nat := 9707472219329282981575

theorem tailTrace_1531324 : CollatzResearch.WordTrace tailWord_1531324 prefixEnd_1531324 9707472219329282981575 := by
  unfold tailWord_1531324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925987352141076081448513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37234649802854768108598017 27925987352141076081448513)
  ·
    refine ⟨20944490514105807061086385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27925987352141076081448513 20944490514105807061086385)
    ·
      refine ⟨15708367885579355295814789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20944490514105807061086385 15708367885579355295814789)
      ·
        refine ⟨2945318978546129117965273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15708367885579355295814789 2945318978546129117965273)
        ·
          refine ⟨2208989233909596838473955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945318978546129117965273 2208989233909596838473955)
          ·
            refine ⟨3313483850864395257710933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208989233909596838473955 3313483850864395257710933)
            ·
              refine ⟨9707472219329282981575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3313483850864395257710933 9707472219329282981575)
              ·
                rfl

theorem cell23_1531324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 10].length) (baseStart_1531324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531324 prefixEnd_1531324 := by exact prefixLift 1531324
  have htrace : WordTrace (prefixWord ++ tailWord_1531324) baseStart_1531324 baseEnd_1531324 := by
    simpa [prefixWord, tailWord_1531324, baseEnd_1531324] using wordTrace_append hprefix tailTrace_1531324
  have hstable : (prefixWord ++ tailWord_1531324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531324).length < 2 ^ (prefixWord ++ tailWord_1531324).sum := by decide
  have hdescent : baseEnd_1531324 < baseStart_1531324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531348 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1531348 : Nat := 118140960795 + 1531348 * 2 ^ 59
def prefixEnd_1531348 : Nat := 4983230072969 + 3 ^ 40 * 1531348 * 2
def baseEnd_1531348 : Nat := 786317573301379827607465

theorem tailTrace_1531348 : CollatzResearch.WordTrace tailWord_1531348 prefixEnd_1531348 786317573301379827607465 := by
  unfold tailWord_1531348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926425028097602130885349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37235233370796802841180465 27926425028097602130885349)
  ·
    refine ⟨5236204692768300399541003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27926425028097602130885349 5236204692768300399541003)
    ·
      refine ⟨7854307039152450599311505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236204692768300399541003 7854307039152450599311505)
      ·
        refine ⟨5890730279364337949483629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7854307039152450599311505 5890730279364337949483629)
        ·
          refine ⟨2209023854761626731056361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5890730279364337949483629 2209023854761626731056361)
          ·
            refine ⟨1656767891071220048292271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209023854761626731056361 1656767891071220048292271)
            ·
              refine ⟨2485151836606830072438407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656767891071220048292271 2485151836606830072438407)
              ·
                refine ⟨3727727754910245108657611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485151836606830072438407 3727727754910245108657611)
                ·
                  refine ⟨5591591632365367662986417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727727754910245108657611 5591591632365367662986417)
                  ·
                    refine ⟨4193693724274025747239813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591591632365367662986417 4193693724274025747239813)
                    ·
                      refine ⟨786317573301379827607465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4193693724274025747239813 786317573301379827607465)
                      ·
                        rfl

theorem cell23_1531348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1531348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531348 prefixEnd_1531348 := by exact prefixLift 1531348
  have htrace : WordTrace (prefixWord ++ tailWord_1531348) baseStart_1531348 baseEnd_1531348 := by
    simpa [prefixWord, tailWord_1531348, baseEnd_1531348] using wordTrace_append hprefix tailTrace_1531348
  have hstable : (prefixWord ++ tailWord_1531348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531348).length < 2 ^ (prefixWord ++ tailWord_1531348).sum := by decide
  have hdescent : baseEnd_1531348 < baseStart_1531348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531351 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1531351 : Nat := 118140960795 + 1531351 * 2 ^ 59
def prefixEnd_1531351 : Nat := 4983230072969 + 3 ^ 40 * 1531351 * 2
def baseEnd_1531351 : Nat := 786319113743343315869951

theorem tailTrace_1531351 : CollatzResearch.WordTrace tailWord_1531351 prefixEnd_1531351 786319113743343315869951 := by
  unfold tailWord_1531351
  simp only [CollatzResearch.WordTrace]
  refine ⟨55852959475184335774129907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37235306316789557182753271 55852959475184335774129907)
  ·
    refine ⟨83779439212776503661194861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55852959475184335774129907 83779439212776503661194861)
    ·
      refine ⟨31417289704791188872948073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83779439212776503661194861 31417289704791188872948073)
      ·
        refine ⟨23562967278593391654711055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31417289704791188872948073 23562967278593391654711055)
        ·
          refine ⟨35344450917890087482066583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23562967278593391654711055 35344450917890087482066583)
          ·
            refine ⟨53016676376835131223099875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35344450917890087482066583 53016676376835131223099875)
            ·
              refine ⟨79525014565252696834649813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53016676376835131223099875 79525014565252696834649813)
              ·
                refine ⟨1863867528873110082062105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79525014565252696834649813 1863867528873110082062105)
                ·
                  refine ⟨1397900646654832561546579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1863867528873110082062105 1397900646654832561546579)
                  ·
                    refine ⟨2096850969982248842319869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1397900646654832561546579 2096850969982248842319869)
                    ·
                      refine ⟨786319113743343315869951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2096850969982248842319869 786319113743343315869951)
                      ·
                        rfl

theorem cell23_1531351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1531351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531351 prefixEnd_1531351 := by exact prefixLift 1531351
  have htrace : WordTrace (prefixWord ++ tailWord_1531351) baseStart_1531351 baseEnd_1531351 := by
    simpa [prefixWord, tailWord_1531351, baseEnd_1531351] using wordTrace_append hprefix tailTrace_1531351
  have hstable : (prefixWord ++ tailWord_1531351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531351).length < 2 ^ (prefixWord ++ tailWord_1531351).sum := by decide
  have hdescent : baseEnd_1531351 < baseStart_1531351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531407 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_1531407 : Nat := 118140960795 + 1531407 * 2 ^ 59
def prefixEnd_1531407 : Nat := 4983230072969 + 3 ^ 40 * 1531407 * 2
def baseEnd_1531407 : Nat := 786347868659995096769693

theorem tailTrace_1531407 : CollatzResearch.WordTrace tailWord_1531407 prefixEnd_1531407 786347868659995096769693 := by
  unfold tailWord_1531407
  simp only [CollatzResearch.WordTrace]
  refine ⟨55855001962981457338168475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37236667975320971558778983 55855001962981457338168475)
  ·
    refine ⟨83782502944472186007252713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55855001962981457338168475 83782502944472186007252713)
    ·
      refine ⟨62836877208354139505439535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83782502944472186007252713 62836877208354139505439535)
      ·
        refine ⟨94255315812531209258159303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62836877208354139505439535 94255315812531209258159303)
        ·
          refine ⟨141382973718796813887238955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94255315812531209258159303 141382973718796813887238955)
          ·
            refine ⟨212074460578195220830858433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141382973718796813887238955 212074460578195220830858433)
            ·
              refine ⟨159055845433646415623143825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212074460578195220830858433 159055845433646415623143825)
              ·
                refine ⟨119291884075234811717357869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159055845433646415623143825 119291884075234811717357869)
                ·
                  refine ⟨44734456528213054394009201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119291884075234811717357869 44734456528213054394009201)
                  ·
                    refine ⟨33550842396159790795506901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44734456528213054394009201 33550842396159790795506901)
                    ·
                      refine ⟨786347868659995096769693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33550842396159790795506901 786347868659995096769693)
                      ·
                        rfl

theorem cell23_1531407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_1531407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531407 prefixEnd_1531407 := by exact prefixLift 1531407
  have htrace : WordTrace (prefixWord ++ tailWord_1531407) baseStart_1531407 baseEnd_1531407 := by
    simpa [prefixWord, tailWord_1531407, baseEnd_1531407] using wordTrace_append hprefix tailTrace_1531407
  have hstable : (prefixWord ++ tailWord_1531407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531407).length < 2 ^ (prefixWord ++ tailWord_1531407).sum := by decide
  have hdescent : baseEnd_1531407 < baseStart_1531407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531448 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 5]
def baseStart_1531448 : Nat := 118140960795 + 1531448 * 2 ^ 59
def prefixEnd_1531448 : Nat := 4983230072969 + 3 ^ 40 * 1531448 * 2
def baseEnd_1531448 : Nat := 87374324596314381817445

theorem tailTrace_1531448 : CollatzResearch.WordTrace tailWord_1531448 prefixEnd_1531448 87374324596314381817445 := by
  unfold tailWord_1531448
  simp only [CollatzResearch.WordTrace]
  refine ⟨27928248677916460670205499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37237664903888614226940665 27928248677916460670205499)
  ·
    refine ⟨41892373016874691005308249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27928248677916460670205499 41892373016874691005308249)
    ·
      refine ⟨31419279762656018253981187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41892373016874691005308249 31419279762656018253981187)
      ·
        refine ⟨47128919643984027380971781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31419279762656018253981187 47128919643984027380971781)
        ·
          refine ⟨8836672433247005133932209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47128919643984027380971781 8836672433247005133932209)
          ·
            refine ⟨6627504324935253850449157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836672433247005133932209 6627504324935253850449157)
            ·
              refine ⟨1242657060925360096959217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6627504324935253850449157 1242657060925360096959217)
              ·
                refine ⟨931992795694020072719413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242657060925360096959217 931992795694020072719413)
                ·
                  refine ⟨87374324596314381817445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931992795694020072719413 87374324596314381817445)
                  ·
                    rfl

theorem cell23_1531448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 5].length) (baseStart_1531448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531448 prefixEnd_1531448 := by exact prefixLift 1531448
  have htrace : WordTrace (prefixWord ++ tailWord_1531448) baseStart_1531448 baseEnd_1531448 := by
    simpa [prefixWord, tailWord_1531448, baseEnd_1531448] using wordTrace_append hprefix tailTrace_1531448
  have hstable : (prefixWord ++ tailWord_1531448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531448).length < 2 ^ (prefixWord ++ tailWord_1531448).sum := by decide
  have hdescent : baseEnd_1531448 < baseStart_1531448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531498 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_1531498 : Nat := 118140960795 + 1531498 * 2 ^ 59
def prefixEnd_1531498 : Nat := 4983230072969 + 3 ^ 40 * 1531498 * 2
def baseEnd_1531498 : Nat := 786394595399554240731775

theorem tailTrace_1531498 : CollatzResearch.WordTrace tailWord_1531498 prefixEnd_1531498 786394595399554240731775 := by
  unfold tailWord_1531498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964580251412944969932787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37238880670434519919820765 13964580251412944969932787)
  ·
    refine ⟨20946870377119417454899181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964580251412944969932787 20946870377119417454899181)
    ·
      refine ⟨7855076391419781545587193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20946870377119417454899181 7855076391419781545587193)
      ·
        refine ⟨5891307293564836159190395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7855076391419781545587193 5891307293564836159190395)
        ·
          refine ⟨8836960940347254238785593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891307293564836159190395 8836960940347254238785593)
          ·
            refine ⟨6627720705260440679089195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836960940347254238785593 6627720705260440679089195)
            ·
              refine ⟨9941581057890661018633793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627720705260440679089195 9941581057890661018633793)
              ·
                refine ⟨7456185793417995763975345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941581057890661018633793 7456185793417995763975345)
                ·
                  refine ⟨5592139345063496822981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7456185793417995763975345 5592139345063496822981509)
                  ·
                    refine ⟨1048526127199405654309033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592139345063496822981509 1048526127199405654309033)
                    ·
                      refine ⟨786394595399554240731775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048526127199405654309033 786394595399554240731775)
                      ·
                        rfl

theorem cell23_1531498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_1531498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531498 prefixEnd_1531498 := by exact prefixLift 1531498
  have htrace : WordTrace (prefixWord ++ tailWord_1531498) baseStart_1531498 baseEnd_1531498 := by
    simpa [prefixWord, tailWord_1531498, baseEnd_1531498] using wordTrace_append hprefix tailTrace_1531498
  have hstable : (prefixWord ++ tailWord_1531498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531498).length < 2 ^ (prefixWord ++ tailWord_1531498).sum := by decide
  have hdescent : baseEnd_1531498 < baseStart_1531498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531571 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4]
def baseStart_1531571 : Nat := 118140960795 + 1531571 * 2 ^ 59
def prefixEnd_1531571 : Nat := 4983230072969 + 3 ^ 40 * 1531571 * 2
def baseEnd_1531571 : Nat := 786432079487332455118939

theorem tailTrace_1531571 : CollatzResearch.WordTrace tailWord_1531571 prefixEnd_1531571 786432079487332455118939 := by
  unfold tailWord_1531571
  simp only [CollatzResearch.WordTrace]
  refine ⟨55860983534387313347138567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37240655689591542231425711 55860983534387313347138567)
  ·
    refine ⟨83791475301580970020707851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55860983534387313347138567 83791475301580970020707851)
    ·
      refine ⟨125687212952371455031061777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83791475301580970020707851 125687212952371455031061777)
      ·
        refine ⟨94265409714278591273296333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125687212952371455031061777 94265409714278591273296333)
        ·
          refine ⟨35349528642854471727486125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94265409714278591273296333 35349528642854471727486125)
          ·
            refine ⟨13256073241070426897807297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35349528642854471727486125 13256073241070426897807297)
            ·
              refine ⟨9942054930802820173355473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13256073241070426897807297 9942054930802820173355473)
              ·
                refine ⟨7456541198102115130016605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9942054930802820173355473 7456541198102115130016605)
                ·
                  refine ⟨2796202949288293173756227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7456541198102115130016605 2796202949288293173756227)
                  ·
                    refine ⟨4194304423932439760634341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2796202949288293173756227 4194304423932439760634341)
                    ·
                      refine ⟨786432079487332455118939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4194304423932439760634341 786432079487332455118939)
                      ·
                        rfl

theorem cell23_1531571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_1531571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531571 prefixEnd_1531571 := by exact prefixLift 1531571
  have htrace : WordTrace (prefixWord ++ tailWord_1531571) baseStart_1531571 baseEnd_1531571 := by
    simpa [prefixWord, tailWord_1531571, baseEnd_1531571] using wordTrace_append hprefix tailTrace_1531571
  have hstable : (prefixWord ++ tailWord_1531571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531571).length < 2 ^ (prefixWord ++ tailWord_1531571).sum := by decide
  have hdescent : baseEnd_1531571 < baseStart_1531571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531581 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1531581 : Nat := 118140960795 + 1531581 * 2 ^ 59
def prefixEnd_1531581 : Nat := 4983230072969 + 3 ^ 40 * 1531581 * 2
def baseEnd_1531581 : Nat := 262145738097959138664631

theorem tailTrace_1531581 : CollatzResearch.WordTrace tailWord_1531581 prefixEnd_1531581 262145738097959138664631 := by
  unfold tailWord_1531581
  simp only [CollatzResearch.WordTrace]
  refine ⟨55861348264351085055002597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37240898842900723370001731 55861348264351085055002597)
  ·
    refine ⟨10474002799565828447812987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55861348264351085055002597 10474002799565828447812987)
    ·
      refine ⟨15711004199348742671719481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10474002799565828447812987 15711004199348742671719481)
      ·
        refine ⟨11783253149511557003789611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15711004199348742671719481 11783253149511557003789611)
        ·
          refine ⟨17674879724267335505684417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783253149511557003789611 17674879724267335505684417)
          ·
            refine ⟨13256159793200501629263313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17674879724267335505684417 13256159793200501629263313)
            ·
              refine ⟨9942119844900376221947485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13256159793200501629263313 9942119844900376221947485)
              ·
                refine ⟨3728294941837641083230307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9942119844900376221947485 3728294941837641083230307)
                ·
                  refine ⟨5592442412756461624845461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728294941837641083230307 5592442412756461624845461)
                  ·
                    refine ⟨262145738097959138664631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5592442412756461624845461 262145738097959138664631)
                    ·
                      rfl

theorem cell23_1531581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1531581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531581 prefixEnd_1531581 := by exact prefixLift 1531581
  have htrace : WordTrace (prefixWord ++ tailWord_1531581) baseStart_1531581 baseEnd_1531581 := by
    simpa [prefixWord, tailWord_1531581, baseEnd_1531581] using wordTrace_append hprefix tailTrace_1531581
  have hstable : (prefixWord ++ tailWord_1531581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531581).length < 2 ^ (prefixWord ++ tailWord_1531581).sum := by decide
  have hdescent : baseEnd_1531581 < baseStart_1531581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531588 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1531588 : Nat := 118140960795 + 1531588 * 2 ^ 59
def prefixEnd_1531588 : Nat := 4983230072969 + 3 ^ 40 * 1531588 * 2
def baseEnd_1531588 : Nat := 786440808658458888606361

theorem tailTrace_1531588 : CollatzResearch.WordTrace tailWord_1531588 prefixEnd_1531588 786440808658458888606361 := by
  unfold tailWord_1531588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27930801787662862625253709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37241069050217150167004945 27930801787662862625253709)
  ·
    refine ⟨10474050670373573484470141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27930801787662862625253709 10474050670373573484470141)
    ·
      refine ⟨3927769001390090056676303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10474050670373573484470141 3927769001390090056676303)
      ·
        refine ⟨5891653502085135085014455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927769001390090056676303 5891653502085135085014455)
        ·
          refine ⟨8837480253127702627521683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891653502085135085014455 8837480253127702627521683)
          ·
            refine ⟨13256220379691553941282525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837480253127702627521683 13256220379691553941282525)
            ·
              refine ⟨4971082642384332727980947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13256220379691553941282525 4971082642384332727980947)
              ·
                refine ⟨7456623963576499091971421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971082642384332727980947 7456623963576499091971421)
                ·
                  refine ⟨2796233986341187159489283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7456623963576499091971421 2796233986341187159489283)
                  ·
                    refine ⟨4194350979511780739233925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2796233986341187159489283 4194350979511780739233925)
                    ·
                      refine ⟨786440808658458888606361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4194350979511780739233925 786440808658458888606361)
                      ·
                        rfl

theorem cell23_1531588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1531588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531588 prefixEnd_1531588 := by exact prefixLift 1531588
  have htrace : WordTrace (prefixWord ++ tailWord_1531588) baseStart_1531588 baseEnd_1531588 := by
    simpa [prefixWord, tailWord_1531588, baseEnd_1531588] using wordTrace_append hprefix tailTrace_1531588
  have hstable : (prefixWord ++ tailWord_1531588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531588).length < 2 ^ (prefixWord ++ tailWord_1531588).sum := by decide
  have hdescent : baseEnd_1531588 < baseStart_1531588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531601 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1531601 : Nat := 118140960795 + 1531601 * 2 ^ 59
def prefixEnd_1531601 : Nat := 4983230072969 + 3 ^ 40 * 1531601 * 2
def baseEnd_1531601 : Nat := 786447483906967337743801

theorem tailTrace_1531601 : CollatzResearch.WordTrace tailWord_1531601 prefixEnd_1531601 786447483906967337743801 := by
  unfold tailWord_1531601
  simp only [CollatzResearch.WordTrace]
  refine ⟨55862077724278628470730657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37241385149519085647153771 55862077724278628470730657)
  ·
    refine ⟨41896558293208971353047993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55862077724278628470730657 41896558293208971353047993)
    ·
      refine ⟨31422418719906728514785995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41896558293208971353047993 31422418719906728514785995)
      ·
        refine ⟨47133628079860092772178993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31422418719906728514785995 47133628079860092772178993)
        ·
          refine ⟨35350221059895069579134245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47133628079860092772178993 35350221059895069579134245)
          ·
            refine ⟨6628166448730325546087671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35350221059895069579134245 6628166448730325546087671)
            ·
              refine ⟨9942249673095488319131507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628166448730325546087671 9942249673095488319131507)
              ·
                refine ⟨14913374509643232478697261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942249673095488319131507 14913374509643232478697261)
                ·
                  refine ⟨5592515441116212179511473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14913374509643232478697261 5592515441116212179511473)
                  ·
                    refine ⟨4194386580837159134633605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592515441116212179511473 4194386580837159134633605)
                    ·
                      refine ⟨786447483906967337743801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4194386580837159134633605 786447483906967337743801)
                      ·
                        rfl

theorem cell23_1531601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1531601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531601 prefixEnd_1531601 := by exact prefixLift 1531601
  have htrace : WordTrace (prefixWord ++ tailWord_1531601) baseStart_1531601 baseEnd_1531601 := by
    simpa [prefixWord, tailWord_1531601, baseEnd_1531601] using wordTrace_append hprefix tailTrace_1531601
  have hstable : (prefixWord ++ tailWord_1531601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531601).length < 2 ^ (prefixWord ++ tailWord_1531601).sum := by decide
  have hdescent : baseEnd_1531601 < baseStart_1531601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531688 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1531688 : Nat := 118140960795 + 1531688 * 2 ^ 59
def prefixEnd_1531688 : Nat := 4983230072969 + 3 ^ 40 * 1531688 * 2
def baseEnd_1531688 : Nat := 262164052241302832451967

theorem tailTrace_1531688 : CollatzResearch.WordTrace tailWord_1531688 prefixEnd_1531688 262164052241302832451967 := by
  unfold tailWord_1531688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932625437481721164573859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37243500583308961552765145 27932625437481721164573859)
  ·
    refine ⟨41898938156222581746860789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932625437481721164573859 41898938156222581746860789)
    ·
      refine ⟨3928025452145867038768199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41898938156222581746860789 3928025452145867038768199)
      ·
        refine ⟨5892038178218800558152299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928025452145867038768199 5892038178218800558152299)
        ·
          refine ⟨8838057267328200837228449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892038178218800558152299 8838057267328200837228449)
          ·
            refine ⟨6628542950496150627921337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8838057267328200837228449 6628542950496150627921337)
            ·
              refine ⟨4971407212872112970941003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6628542950496150627921337 4971407212872112970941003)
              ·
                refine ⟨7457110819308169456411505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971407212872112970941003 7457110819308169456411505)
                ·
                  refine ⟨5592833114481127092308629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457110819308169456411505 5592833114481127092308629)
                  ·
                    refine ⟨262164052241302832451967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5592833114481127092308629 262164052241302832451967)
                    ·
                      rfl

theorem cell23_1531688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1531688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531688 prefixEnd_1531688 := by exact prefixLift 1531688
  have htrace : WordTrace (prefixWord ++ tailWord_1531688) baseStart_1531688 baseEnd_1531688 := by
    simpa [prefixWord, tailWord_1531688, baseEnd_1531688] using wordTrace_append hprefix tailTrace_1531688
  have hstable : (prefixWord ++ tailWord_1531688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531688).length < 2 ^ (prefixWord ++ tailWord_1531688).sum := by decide
  have hdescent : baseEnd_1531688 < baseStart_1531688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531691 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_1531691 : Nat := 118140960795 + 1531691 * 2 ^ 59
def prefixEnd_1531691 : Nat := 4983230072969 + 3 ^ 40 * 1531691 * 2
def baseEnd_1531691 : Nat := 786493697165871985618387

theorem tailTrace_1531691 : CollatzResearch.WordTrace tailWord_1531691 prefixEnd_1531691 786493697165871985618387 := by
  unfold tailWord_1531691
  simp only [CollatzResearch.WordTrace]
  refine ⟨55865360293952573841506927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37243573529301715894337951 55865360293952573841506927)
  ·
    refine ⟨83798040440928860762260391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55865360293952573841506927 83798040440928860762260391)
    ·
      refine ⟨125697060661393291143390587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83798040440928860762260391 125697060661393291143390587)
      ·
        refine ⟨188545590992089936715085881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125697060661393291143390587 188545590992089936715085881)
        ·
          refine ⟨141409193244067452536314411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188545590992089936715085881 141409193244067452536314411)
          ·
            refine ⟨212113789866101178804471617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141409193244067452536314411 212113789866101178804471617)
            ·
              refine ⟨159085342399575884103353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212113789866101178804471617 159085342399575884103353713)
              ·
                refine ⟨119314006799681913077515285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159085342399575884103353713 119314006799681913077515285)
                ·
                  refine ⟨5592844068735089675508529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119314006799681913077515285 5592844068735089675508529)
                  ·
                    refine ⟨4194633051551317256631397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592844068735089675508529 4194633051551317256631397)
                    ·
                      refine ⟨786493697165871985618387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4194633051551317256631397 786493697165871985618387)
                      ·
                        rfl

theorem cell23_1531691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_1531691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531691 prefixEnd_1531691 := by exact prefixLift 1531691
  have htrace : WordTrace (prefixWord ++ tailWord_1531691) baseStart_1531691 baseEnd_1531691 := by
    simpa [prefixWord, tailWord_1531691, baseEnd_1531691] using wordTrace_append hprefix tailTrace_1531691
  have hstable : (prefixWord ++ tailWord_1531691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531691).length < 2 ^ (prefixWord ++ tailWord_1531691).sum := by decide
  have hdescent : baseEnd_1531691 < baseStart_1531691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531735 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 7]
def baseStart_1531735 : Nat := 118140960795 + 1531735 * 2 ^ 59
def prefixEnd_1531735 : Nat := 4983230072969 + 3 ^ 40 * 1531735 * 2
def baseEnd_1531735 : Nat := 87390698923852201496465

theorem tailTrace_1531735 : CollatzResearch.WordTrace tailWord_1531735 prefixEnd_1531735 87390698923852201496465 := by
  unfold tailWord_1531735
  simp only [CollatzResearch.WordTrace]
  refine ⟨55866965105793169356108659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37244643403862112904072439 55866965105793169356108659)
  ·
    refine ⟨83800447658689754034162989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55866965105793169356108659 83800447658689754034162989)
    ·
      refine ⟨31425167872008657762811121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83800447658689754034162989 31425167872008657762811121)
      ·
        refine ⟨23568875904006493322108341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31425167872008657762811121 23568875904006493322108341)
        ·
          refine ⟨2209582116000608748947657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23568875904006493322108341 2209582116000608748947657)
          ·
            refine ⟨1657186587000456561710743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209582116000608748947657 1657186587000456561710743)
            ·
              refine ⟨2485779880500684842566115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657186587000456561710743 2485779880500684842566115)
              ·
                refine ⟨3728669820751027263849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485779880500684842566115 3728669820751027263849173)
                ·
                  refine ⟨87390698923852201496465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3728669820751027263849173 87390698923852201496465)
                  ·
                    rfl

theorem cell23_1531735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 7].length) (baseStart_1531735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531735 prefixEnd_1531735 := by exact prefixLift 1531735
  have htrace : WordTrace (prefixWord ++ tailWord_1531735) baseStart_1531735 baseEnd_1531735 := by
    simpa [prefixWord, tailWord_1531735, baseEnd_1531735] using wordTrace_append hprefix tailTrace_1531735
  have hstable : (prefixWord ++ tailWord_1531735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531735).length < 2 ^ (prefixWord ++ tailWord_1531735).sum := by decide
  have hdescent : baseEnd_1531735 < baseStart_1531735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531746 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1531746 : Nat := 118140960795 + 1531746 * 2 ^ 59
def prefixEnd_1531746 : Nat := 4983230072969 + 3 ^ 40 * 1531746 * 2
def baseEnd_1531746 : Nat := 786521938601869270430635

theorem tailTrace_1531746 : CollatzResearch.WordTrace tailWord_1531746 prefixEnd_1531746 786521938601869270430635 := by
  unfold tailWord_1531746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966841577188329558689773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37244910872502212156506061 13966841577188329558689773)
  ·
    refine ⟨5237565591445623584508665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13966841577188329558689773 5237565591445623584508665)
    ·
      refine ⟨3928174193584217688381499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237565591445623584508665 3928174193584217688381499)
      ·
        refine ⟨5892261290376326532572249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928174193584217688381499 5892261290376326532572249)
        ·
          refine ⟨4419195967782244899429187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5892261290376326532572249 4419195967782244899429187)
          ·
            refine ⟨6628793951673367349143781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419195967782244899429187 6628793951673367349143781)
            ·
              refine ⟨1242898865938756377964459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6628793951673367349143781 1242898865938756377964459)
              ·
                refine ⟨1864348298908134566946689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242898865938756377964459 1864348298908134566946689)
                ·
                  refine ⟨1398261224181100925210017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864348298908134566946689 1398261224181100925210017)
                  ·
                    refine ⟨1048695918135825693907513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398261224181100925210017 1048695918135825693907513)
                    ·
                      refine ⟨786521938601869270430635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048695918135825693907513 786521938601869270430635)
                      ·
                        rfl

theorem cell23_1531746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1531746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531746 prefixEnd_1531746 := by exact prefixLift 1531746
  have htrace : WordTrace (prefixWord ++ tailWord_1531746) baseStart_1531746 baseEnd_1531746 := by
    simpa [prefixWord, tailWord_1531746, baseEnd_1531746] using wordTrace_append hprefix tailTrace_1531746
  have hstable : (prefixWord ++ tailWord_1531746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531746).length < 2 ^ (prefixWord ++ tailWord_1531746).sum := by decide
  have hdescent : baseEnd_1531746 < baseStart_1531746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531765 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1531765 : Nat := 118140960795 + 1531765 * 2 ^ 59
def prefixEnd_1531765 : Nat := 4983230072969 + 3 ^ 40 * 1531765 * 2
def baseEnd_1531765 : Nat := 262177231578101565364349

theorem tailTrace_1531765 : CollatzResearch.WordTrace tailWord_1531765 prefixEnd_1531765 262177231578101565364349 := by
  unfold tailWord_1531765
  simp only [CollatzResearch.WordTrace]
  refine ⟨55868059295684484479700749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37245372863789656319800499 55868059295684484479700749)
  ·
    refine ⟨20950522235881681679887781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55868059295684484479700749 20950522235881681679887781)
    ·
      refine ⟨3928222919227815314978959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20950522235881681679887781 3928222919227815314978959)
      ·
        refine ⟨5892334378841722972468439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928222919227815314978959 5892334378841722972468439)
        ·
          refine ⟨8838501568262584458702659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892334378841722972468439 8838501568262584458702659)
          ·
            refine ⟨13257752352393876688053989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838501568262584458702659 13257752352393876688053989)
            ·
              refine ⟨2485828566073851879010123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13257752352393876688053989 2485828566073851879010123)
              ·
                refine ⟨3728742849110777818515185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485828566073851879010123 3728742849110777818515185)
                ·
                  refine ⟨2796557136833083363886389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728742849110777818515185 2796557136833083363886389)
                  ·
                    refine ⟨262177231578101565364349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2796557136833083363886389 262177231578101565364349)
                    ·
                      rfl

theorem cell23_1531765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1531765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531765 prefixEnd_1531765 := by exact prefixLift 1531765
  have htrace : WordTrace (prefixWord ++ tailWord_1531765) baseStart_1531765 baseEnd_1531765 := by
    simpa [prefixWord, tailWord_1531765, baseEnd_1531765] using wordTrace_append hprefix tailTrace_1531765
  have hstable : (prefixWord ++ tailWord_1531765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531765).length < 2 ^ (prefixWord ++ tailWord_1531765).sum := by decide
  have hdescent : baseEnd_1531765 < baseStart_1531765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531785 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 4, 2]
def baseStart_1531785 : Nat := 118140960795 + 1531785 * 2 ^ 59
def prefixEnd_1531785 : Nat := 4983230072969 + 3 ^ 40 * 1531785 * 2
def baseEnd_1531785 : Nat := 786541964347394617842955

theorem tailTrace_1531785 : CollatzResearch.WordTrace tailWord_1531785 prefixEnd_1531785 786541964347394617842955 := by
  unfold tailWord_1531785
  simp only [CollatzResearch.WordTrace]
  refine ⟨55868788755612027895428809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37245859170408018596952539 55868788755612027895428809)
  ·
    refine ⟨41901591566709020921571607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55868788755612027895428809 41901591566709020921571607)
    ·
      refine ⟨62852387350063531382357411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41901591566709020921571607 62852387350063531382357411)
      ·
        refine ⟨94278581025095297073536117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62852387350063531382357411 94278581025095297073536117)
        ·
          refine ⟨8838616971102684100644011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94278581025095297073536117 8838616971102684100644011)
          ·
            refine ⟨13257925456654026150966017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838616971102684100644011 13257925456654026150966017)
            ·
              refine ⟨9943444092490519613224513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13257925456654026150966017 9943444092490519613224513)
              ·
                refine ⟨7457583069367889709918385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9943444092490519613224513 7457583069367889709918385)
                ·
                  refine ⟨5593187302025917282438789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457583069367889709918385 5593187302025917282438789)
                  ·
                    refine ⟨1048722619129859490457273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593187302025917282438789 1048722619129859490457273)
                    ·
                      refine ⟨786541964347394617842955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048722619129859490457273 786541964347394617842955)
                      ·
                        rfl

theorem cell23_1531785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4, 2].length) (baseStart_1531785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531785 prefixEnd_1531785 := by exact prefixLift 1531785
  have htrace : WordTrace (prefixWord ++ tailWord_1531785) baseStart_1531785 baseEnd_1531785 := by
    simpa [prefixWord, tailWord_1531785, baseEnd_1531785] using wordTrace_append hprefix tailTrace_1531785
  have hstable : (prefixWord ++ tailWord_1531785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531785).length < 2 ^ (prefixWord ++ tailWord_1531785).sum := by decide
  have hdescent : baseEnd_1531785 < baseStart_1531785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531786 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_1531786 : Nat := 118140960795 + 1531786 * 2 ^ 59
def prefixEnd_1531786 : Nat := 4983230072969 + 3 ^ 40 * 1531786 * 2
def baseEnd_1531786 : Nat := 87393608647561012658939

theorem tailTrace_1531786 : CollatzResearch.WordTrace tailWord_1531786 prefixEnd_1531786 87393608647561012658939 := by
  unfold tailWord_1531786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13967206307152101266553803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37245883485738936710810141 13967206307152101266553803)
  ·
    refine ⟨20950809460728151899830705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13967206307152101266553803 20950809460728151899830705)
    ·
      refine ⟨15713107095546113924873029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20950809460728151899830705 15713107095546113924873029)
      ·
        refine ⟨2946207580414896360913693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15713107095546113924873029 2946207580414896360913693)
        ·
          refine ⟨1104827842655586135342635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946207580414896360913693 1104827842655586135342635)
          ·
            refine ⟨1657241763983379203013953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104827842655586135342635 1657241763983379203013953)
            ·
              refine ⟨1242931322987534402260465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657241763983379203013953 1242931322987534402260465)
              ·
                refine ⟨932198492240650801695349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242931322987534402260465 932198492240650801695349)
                ·
                  refine ⟨87393608647561012658939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932198492240650801695349 87393608647561012658939)
                  ·
                    rfl

theorem cell23_1531786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_1531786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531786 prefixEnd_1531786 := by exact prefixLift 1531786
  have htrace : WordTrace (prefixWord ++ tailWord_1531786) baseStart_1531786 baseEnd_1531786 := by
    simpa [prefixWord, tailWord_1531786, baseEnd_1531786] using wordTrace_append hprefix tailTrace_1531786
  have hstable : (prefixWord ++ tailWord_1531786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531786).length < 2 ^ (prefixWord ++ tailWord_1531786).sum := by decide
  have hdescent : baseEnd_1531786 < baseStart_1531786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531788 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1531788 : Nat := 118140960795 + 1531788 * 2 ^ 59
def prefixEnd_1531788 : Nat := 4983230072969 + 3 ^ 40 * 1531788 * 2
def baseEnd_1531788 : Nat := 786543504789358106105441

theorem tailTrace_1531788 : CollatzResearch.WordTrace tailWord_1531788 prefixEnd_1531788 786543504789358106105441 := by
  unfold tailWord_1531788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934449087300579703894009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37245932116400772938525345 27934449087300579703894009)
  ·
    refine ⟨20950836815475434777920507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27934449087300579703894009 20950836815475434777920507)
    ·
      refine ⟨31426255223213152166880761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20950836815475434777920507 31426255223213152166880761)
      ·
        refine ⟨23569691417409864125160571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31426255223213152166880761 23569691417409864125160571)
        ·
          refine ⟨35354537126114796187740857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23569691417409864125160571 35354537126114796187740857)
          ·
            refine ⟨26515902844586097140805643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35354537126114796187740857 26515902844586097140805643)
            ·
              refine ⟨39773854266879145711208465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515902844586097140805643 39773854266879145711208465)
              ·
                refine ⟨29830390700159359283406349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39773854266879145711208465 29830390700159359283406349)
                ·
                  refine ⟨11186396512559759731277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29830390700159359283406349 11186396512559759731277381)
                  ·
                    refine ⟨2097449346104954949614509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11186396512559759731277381 2097449346104954949614509)
                    ·
                      refine ⟨786543504789358106105441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097449346104954949614509 786543504789358106105441)
                      ·
                        rfl

theorem cell23_1531788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1531788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531788 prefixEnd_1531788 := by exact prefixLift 1531788
  have htrace : WordTrace (prefixWord ++ tailWord_1531788) baseStart_1531788 baseEnd_1531788 := by
    simpa [prefixWord, tailWord_1531788, baseEnd_1531788] using wordTrace_append hprefix tailTrace_1531788
  have hstable : (prefixWord ++ tailWord_1531788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531788).length < 2 ^ (prefixWord ++ tailWord_1531788).sum := by decide
  have hdescent : baseEnd_1531788 < baseStart_1531788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531791 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 14]
def baseStart_1531791 : Nat := 118140960795 + 1531791 * 2 ^ 59
def prefixEnd_1531791 : Nat := 4983230072969 + 3 ^ 40 * 1531791 * 2
def baseEnd_1531791 : Nat := 87393893914591288263103

theorem tailTrace_1531791 : CollatzResearch.WordTrace tailWord_1531791 prefixEnd_1531791 87393893914591288263103 := by
  unfold tailWord_1531791
  simp only [CollatzResearch.WordTrace]
  refine ⟨55869007593590290920147227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37246005062393527280098151 55869007593590290920147227)
  ·
    refine ⟨83803511390385436380220841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55869007593590290920147227 83803511390385436380220841)
    ·
      refine ⟨62852633542789077285165631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83803511390385436380220841 62852633542789077285165631)
      ·
        refine ⟨94278950314183615927748447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62852633542789077285165631 94278950314183615927748447)
        ·
          refine ⟨141418425471275423891622671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94278950314183615927748447 141418425471275423891622671)
          ·
            refine ⟨212127638206913135837434007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141418425471275423891622671 212127638206913135837434007)
            ·
              refine ⟨318191457310369703756151011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212127638206913135837434007 318191457310369703756151011)
              ·
                refine ⟨477287185965554555634226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318191457310369703756151011 477287185965554555634226517)
                ·
                  refine ⟨87393893914591288263103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 477287185965554555634226517 87393893914591288263103)
                  ·
                    rfl

theorem cell23_1531791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 14].length) (baseStart_1531791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531791 prefixEnd_1531791 := by exact prefixLift 1531791
  have htrace : WordTrace (prefixWord ++ tailWord_1531791) baseStart_1531791 baseEnd_1531791 := by
    simpa [prefixWord, tailWord_1531791, baseEnd_1531791] using wordTrace_append hprefix tailTrace_1531791
  have hstable : (prefixWord ++ tailWord_1531791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531791).length < 2 ^ (prefixWord ++ tailWord_1531791).sum := by decide
  have hdescent : baseEnd_1531791 < baseStart_1531791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531802 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1531802 : Nat := 118140960795 + 1531802 * 2 ^ 59
def prefixEnd_1531802 : Nat := 4983230072969 + 3 ^ 40 * 1531802 * 2
def baseEnd_1531802 : Nat := 786550693518521051330377

theorem tailTrace_1531802 : CollatzResearch.WordTrace tailWord_1531802 prefixEnd_1531802 786550693518521051330377 := by
  unfold tailWord_1531802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13967352199137609949699415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37246272531033626532531773 13967352199137609949699415)
  ·
    refine ⟨20951028298706414924549123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13967352199137609949699415 20951028298706414924549123)
    ·
      refine ⟨31426542448059622386823685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20951028298706414924549123 31426542448059622386823685)
      ·
        refine ⟨5892476709011179197529441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31426542448059622386823685 5892476709011179197529441)
        ·
          refine ⟨4419357531758384398147081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5892476709011179197529441 4419357531758384398147081)
          ·
            refine ⟨3314518148818788298610311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4419357531758384398147081 3314518148818788298610311)
            ·
              refine ⟨4971777223228182447915467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314518148818788298610311 4971777223228182447915467)
              ·
                refine ⟨7457665834842273671873201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971777223228182447915467 7457665834842273671873201)
                ·
                  refine ⟨5593249376131705253904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457665834842273671873201 5593249376131705253904901)
                  ·
                    refine ⟨1048734258024694735107169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593249376131705253904901 1048734258024694735107169)
                    ·
                      refine ⟨786550693518521051330377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048734258024694735107169 786550693518521051330377)
                      ·
                        rfl

theorem cell23_1531802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1531802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531802 prefixEnd_1531802 := by exact prefixLift 1531802
  have htrace : WordTrace (prefixWord ++ tailWord_1531802) baseStart_1531802 baseEnd_1531802 := by
    simpa [prefixWord, tailWord_1531802, baseEnd_1531802] using wordTrace_append hprefix tailTrace_1531802
  have hstable : (prefixWord ++ tailWord_1531802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531802).length < 2 ^ (prefixWord ++ tailWord_1531802).sum := by decide
  have hdescent : baseEnd_1531802 < baseStart_1531802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531816 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1531816 : Nat := 118140960795 + 1531816 * 2 ^ 59
def prefixEnd_1531816 : Nat := 4983230072969 + 3 ^ 40 * 1531816 * 2
def baseEnd_1531816 : Nat := 262185960749227998851771

theorem tailTrace_1531816 : CollatzResearch.WordTrace tailWord_1531816 prefixEnd_1531816 262185960749227998851771 := by
  unfold tailWord_1531816
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934959709249860094903651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37246612945666480126538201 27934959709249860094903651)
  ·
    refine ⟨41902439563874790142355477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27934959709249860094903651 41902439563874790142355477)
    ·
      refine ⟨1964176854556630787922913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41902439563874790142355477 1964176854556630787922913)
      ·
        refine ⟨1473132640917473090942185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964176854556630787922913 1473132640917473090942185)
        ·
          refine ⟨1104849480688104818206639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473132640917473090942185 1104849480688104818206639)
          ·
            refine ⟨1657274221032157227309959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104849480688104818206639 1657274221032157227309959)
            ·
              refine ⟨2485911331548235840964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657274221032157227309959 2485911331548235840964939)
              ·
                refine ⟨3728866997322353761447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485911331548235840964939 3728866997322353761447409)
                ·
                  refine ⟨2796650247991765321085557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728866997322353761447409 2796650247991765321085557)
                  ·
                    refine ⟨262185960749227998851771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2796650247991765321085557 262185960749227998851771)
                    ·
                      rfl

theorem cell23_1531816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1531816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531816 prefixEnd_1531816 := by exact prefixLift 1531816
  have htrace : WordTrace (prefixWord ++ tailWord_1531816) baseStart_1531816 baseEnd_1531816 := by
    simpa [prefixWord, tailWord_1531816, baseEnd_1531816] using wordTrace_append hprefix tailTrace_1531816
  have hstable : (prefixWord ++ tailWord_1531816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531816).length < 2 ^ (prefixWord ++ tailWord_1531816).sum := by decide
  have hdescent : baseEnd_1531816 < baseStart_1531816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531829 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1531829 : Nat := 118140960795 + 1531829 * 2 ^ 59
def prefixEnd_1531829 : Nat := 4983230072969 + 3 ^ 40 * 1531829 * 2
def baseEnd_1531829 : Nat := 262188185832064148564251

theorem tailTrace_1531829 : CollatzResearch.WordTrace tailWord_1531829 prefixEnd_1531829 262188185832064148564251 := by
  unfold tailWord_1531829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55870393567452623410030541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37246929044968415606687027 55870393567452623410030541)
  ·
    refine ⟨20951397587794733778761453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55870393567452623410030541 20951397587794733778761453)
    ·
      refine ⟨7856774095423025167035545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20951397587794733778761453 7856774095423025167035545)
      ·
        refine ⟨5892580571567268875276659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7856774095423025167035545 5892580571567268875276659)
        ·
          refine ⟨8838870857350903312914989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892580571567268875276659 8838870857350903312914989)
          ·
            refine ⟨3314576571506588742343121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8838870857350903312914989 3314576571506588742343121)
            ·
              refine ⟨2485932428629941556757341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314576571506588742343121 2485932428629941556757341)
              ·
                refine ⟨932224660736228083784003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2485932428629941556757341 932224660736228083784003)
                ·
                  refine ⟨1398336991104342125676005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932224660736228083784003 1398336991104342125676005)
                  ·
                    refine ⟨262188185832064148564251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398336991104342125676005 262188185832064148564251)
                    ·
                      rfl

theorem cell23_1531829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1531829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531829 prefixEnd_1531829 := by exact prefixLift 1531829
  have htrace : WordTrace (prefixWord ++ tailWord_1531829) baseStart_1531829 baseEnd_1531829 := by
    simpa [prefixWord, tailWord_1531829, baseEnd_1531829] using wordTrace_append hprefix tailTrace_1531829
  have hstable : (prefixWord ++ tailWord_1531829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531829).length < 2 ^ (prefixWord ++ tailWord_1531829).sum := by decide
  have hdescent : baseEnd_1531829 < baseStart_1531829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531852 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1531852 : Nat := 118140960795 + 1531852 * 2 ^ 59
def prefixEnd_1531852 : Nat := 4983230072969 + 3 ^ 40 * 1531852 * 2
def baseEnd_1531852 : Nat := 786576367551245855705147

theorem tailTrace_1531852 : CollatzResearch.WordTrace tailWord_1531852 prefixEnd_1531852 786576367551245855705147 := by
  unfold tailWord_1531852
  simp only [CollatzResearch.WordTrace]
  refine ⟨27935616223184649169058905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37247488297579532225411873 27935616223184649169058905)
  ·
    refine ⟨20951712167388486876794179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27935616223184649169058905 20951712167388486876794179)
    ·
      refine ⟨31427568251082730315191269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20951712167388486876794179 31427568251082730315191269)
      ·
        refine ⟨5892669047078011934098363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31427568251082730315191269 5892669047078011934098363)
        ·
          refine ⟨8839003570617017901147545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892669047078011934098363 8839003570617017901147545)
          ·
            refine ⟨6629252677962763425860659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839003570617017901147545 6629252677962763425860659)
            ·
              refine ⟨9943879016944145138790989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629252677962763425860659 9943879016944145138790989)
              ·
                refine ⟨3728954631354054427046621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9943879016944145138790989 3728954631354054427046621)
                ·
                  refine ⟨1398357986757770410142483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3728954631354054427046621 1398357986757770410142483)
                  ·
                    refine ⟨2097536980136655615213725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398357986757770410142483 2097536980136655615213725)
                    ·
                      refine ⟨786576367551245855705147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097536980136655615213725 786576367551245855705147)
                      ·
                        rfl

theorem cell23_1531852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1531852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531852 prefixEnd_1531852 := by exact prefixLift 1531852
  have htrace : WordTrace (prefixWord ++ tailWord_1531852) baseStart_1531852 baseEnd_1531852 := by
    simpa [prefixWord, tailWord_1531852, baseEnd_1531852] using wordTrace_append hprefix tailTrace_1531852
  have hstable : (prefixWord ++ tailWord_1531852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531852).length < 2 ^ (prefixWord ++ tailWord_1531852).sum := by decide
  have hdescent : baseEnd_1531852 < baseStart_1531852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531886 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_1531886 : Nat := 118140960795 + 1531886 * 2 ^ 59
def prefixEnd_1531886 : Nat := 4983230072969 + 3 ^ 40 * 1531886 * 2
def baseEnd_1531886 : Nat := 786593825893498722679991

theorem tailTrace_1531886 : CollatzResearch.WordTrace tailWord_1531886 prefixEnd_1531886 786593825893498722679991 := by
  unfold tailWord_1531886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984059066030765268106939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37248315018830748096570341 6984059066030765268106939)
  ·
    refine ⟨10476088599046147902160409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6984059066030765268106939 10476088599046147902160409)
    ·
      refine ⟨7857066449284610926620307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10476088599046147902160409 7857066449284610926620307)
      ·
        refine ⟨11785599673926916389930461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857066449284610926620307 11785599673926916389930461)
        ·
          refine ⟨4419599877722593646223923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11785599673926916389930461 4419599877722593646223923)
          ·
            refine ⟨6629399816583890469335885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419599877722593646223923 6629399816583890469335885)
            ·
              refine ⟨2486024931218958926000957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6629399816583890469335885 2486024931218958926000957)
              ·
                refine ⟨932259349207109597250359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486024931218958926000957 932259349207109597250359)
                ·
                  refine ⟨1398389023810664395875539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932259349207109597250359 1398389023810664395875539)
                  ·
                    refine ⟨2097583535715996593813309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398389023810664395875539 2097583535715996593813309)
                    ·
                      refine ⟨786593825893498722679991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097583535715996593813309 786593825893498722679991)
                      ·
                        rfl

theorem cell23_1531886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_1531886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531886 prefixEnd_1531886 := by exact prefixLift 1531886
  have htrace : WordTrace (prefixWord ++ tailWord_1531886) baseStart_1531886 baseEnd_1531886 := by
    simpa [prefixWord, tailWord_1531886, baseEnd_1531886] using wordTrace_append hprefix tailTrace_1531886
  have hstable : (prefixWord ++ tailWord_1531886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531886).length < 2 ^ (prefixWord ++ tailWord_1531886).sum := by decide
  have hdescent : baseEnd_1531886 < baseStart_1531886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531909 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_1531909 : Nat := 118140960795 + 1531909 * 2 ^ 59
def prefixEnd_1531909 : Nat := 4983230072969 + 3 ^ 40 * 1531909 * 2
def baseEnd_1531909 : Nat := 786605635948552132692385

theorem tailTrace_1531909 : CollatzResearch.WordTrace tailWord_1531909 prefixEnd_1531909 786605635948552132692385 := by
  unfold tailWord_1531909
  simp only [CollatzResearch.WordTrace]
  refine ⟨55873311407162797072942781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37248874271441864715295187 55873311407162797072942781)
  ·
    refine ⟨20952491777686048902353543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55873311407162797072942781 20952491777686048902353543)
    ·
      refine ⟨31428737666529073353530315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20952491777686048902353543 31428737666529073353530315)
      ·
        refine ⟨47143106499793610030295473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31428737666529073353530315 47143106499793610030295473)
        ·
          refine ⟨35357329874845207522721605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47143106499793610030295473 35357329874845207522721605)
          ·
            refine ⟨6629499351533476410510301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35357329874845207522721605 6629499351533476410510301)
            ·
              refine ⟨2486062256825053653941363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6629499351533476410510301 2486062256825053653941363)
              ·
                refine ⟨3729093385237580480912045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486062256825053653941363 3729093385237580480912045)
                ·
                  refine ⟨1398410019464092680342017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729093385237580480912045 1398410019464092680342017)
                  ·
                    refine ⟨1048807514598069510256513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398410019464092680342017 1048807514598069510256513)
                    ·
                      refine ⟨786605635948552132692385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048807514598069510256513 786605635948552132692385)
                      ·
                        rfl

theorem cell23_1531909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_1531909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531909 prefixEnd_1531909 := by exact prefixLift 1531909
  have htrace : WordTrace (prefixWord ++ tailWord_1531909) baseStart_1531909 baseEnd_1531909 := by
    simpa [prefixWord, tailWord_1531909, baseEnd_1531909] using wordTrace_append hprefix tailTrace_1531909
  have hstable : (prefixWord ++ tailWord_1531909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531909).length < 2 ^ (prefixWord ++ tailWord_1531909).sum := by decide
  have hdescent : baseEnd_1531909 < baseStart_1531909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531910 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1531910 : Nat := 118140960795 + 1531910 * 2 ^ 59
def prefixEnd_1531910 : Nat := 4983230072969 + 3 ^ 40 * 1531910 * 2
def baseEnd_1531910 : Nat := 87400683269911847642209

theorem tailTrace_1531910 : CollatzResearch.WordTrace tailWord_1531910 prefixEnd_1531910 87400683269911847642209 := by
  unfold tailWord_1531910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746042121254974195116537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37248898586772782829152789 1746042121254974195116537)
  ·
    refine ⟨1309531590941230646337403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1746042121254974195116537 1309531590941230646337403)
    ·
      refine ⟨1964297386411845969506105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309531590941230646337403 1964297386411845969506105)
      ·
        refine ⟨1473223039808884477129579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964297386411845969506105 1473223039808884477129579)
        ·
          refine ⟨2209834559713326715694369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473223039808884477129579 2209834559713326715694369)
          ·
            refine ⟨1657375919784995036770777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209834559713326715694369 1657375919784995036770777)
            ·
              refine ⟨1243031939838746277578083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657375919784995036770777 1243031939838746277578083)
              ·
                refine ⟨1864547909758119416367125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243031939838746277578083 1864547909758119416367125)
                ·
                  refine ⟨87400683269911847642209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1864547909758119416367125 87400683269911847642209)
                  ·
                    rfl

theorem cell23_1531910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1531910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531910 prefixEnd_1531910 := by exact prefixLift 1531910
  have htrace : WordTrace (prefixWord ++ tailWord_1531910) baseStart_1531910 baseEnd_1531910 := by
    simpa [prefixWord, tailWord_1531910, baseEnd_1531910] using wordTrace_append hprefix tailTrace_1531910
  have hstable : (prefixWord ++ tailWord_1531910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531910).length < 2 ^ (prefixWord ++ tailWord_1531910).sum := by decide
  have hdescent : baseEnd_1531910 < baseStart_1531910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531946 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1531946 : Nat := 118140960795 + 1531946 * 2 ^ 59
def prefixEnd_1531946 : Nat := 4983230072969 + 3 ^ 40 * 1531946 * 2
def baseEnd_1531946 : Nat := 786624634732768487929715

theorem tailTrace_1531946 : CollatzResearch.WordTrace tailWord_1531946 prefixEnd_1531946 786624634732768487929715 := by
  unfold tailWord_1531946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968665227007188098009923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37249773938685834928026461 13968665227007188098009923)
  ·
    refine ⟨20952997840510782147014885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13968665227007188098009923 20952997840510782147014885)
    ·
      refine ⟨3928687095095771652565291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20952997840510782147014885 3928687095095771652565291)
      ·
        refine ⟨5893030642643657478847937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928687095095771652565291 5893030642643657478847937)
        ·
          refine ⟨4419772981982743109135953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893030642643657478847937 4419772981982743109135953)
          ·
            refine ⟨3314829736487057331851965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4419772981982743109135953 3314829736487057331851965)
            ·
              refine ⟨1243061151182646499444487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3314829736487057331851965 1243061151182646499444487)
              ·
                refine ⟨1864591726773969749166731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243061151182646499444487 1864591726773969749166731)
                ·
                  refine ⟨2796887590160954623750097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864591726773969749166731 2796887590160954623750097)
                  ·
                    refine ⟨2097665692620715967812573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2796887590160954623750097 2097665692620715967812573)
                    ·
                      refine ⟨786624634732768487929715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097665692620715967812573 786624634732768487929715)
                      ·
                        rfl

theorem cell23_1531946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1531946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531946 prefixEnd_1531946 := by exact prefixLift 1531946
  have htrace : WordTrace (prefixWord ++ tailWord_1531946) baseStart_1531946 baseEnd_1531946 := by
    simpa [prefixWord, tailWord_1531946, baseEnd_1531946] using wordTrace_append hprefix tailTrace_1531946
  have hstable : (prefixWord ++ tailWord_1531946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531946).length < 2 ^ (prefixWord ++ tailWord_1531946).sum := by decide
  have hdescent : baseEnd_1531946 < baseStart_1531946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531960 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_1531960 : Nat := 118140960795 + 1531960 * 2 ^ 59
def prefixEnd_1531960 : Nat := 4983230072969 + 3 ^ 40 * 1531960 * 2
def baseEnd_1531960 : Nat := 786631823461931433154651

theorem tailTrace_1531960 : CollatzResearch.WordTrace tailWord_1531960 prefixEnd_1531960 786631823461931433154651 := by
  unfold tailWord_1531960
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937585764989016391524667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37250114353318688522032889 27937585764989016391524667)
  ·
    refine ⟨41906378647483524587287001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27937585764989016391524667 41906378647483524587287001)
    ·
      refine ⟨31429783985612643440465251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41906378647483524587287001 31429783985612643440465251)
      ·
        refine ⟨47144675978418965160697877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31429783985612643440465251 47144675978418965160697877)
        ·
          refine ⟨2209906686488388991907713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47144675978418965160697877 2209906686488388991907713)
          ·
            refine ⟨1657430014866291743930785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209906686488388991907713 1657430014866291743930785)
            ·
              refine ⟨1243072511149718807948089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657430014866291743930785 1243072511149718807948089)
              ·
                refine ⟨932304383362289105961067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243072511149718807948089 932304383362289105961067)
                ·
                  refine ⟨1398456575043433658941601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932304383362289105961067 1398456575043433658941601)
                  ·
                    refine ⟨1048842431282575244206201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398456575043433658941601 1048842431282575244206201)
                    ·
                      refine ⟨786631823461931433154651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048842431282575244206201 786631823461931433154651)
                      ·
                        rfl

theorem cell23_1531960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_1531960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531960 prefixEnd_1531960 := by exact prefixLift 1531960
  have htrace : WordTrace (prefixWord ++ tailWord_1531960) baseStart_1531960 baseEnd_1531960 := by
    simpa [prefixWord, tailWord_1531960, baseEnd_1531960] using wordTrace_append hprefix tailTrace_1531960
  have hstable : (prefixWord ++ tailWord_1531960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531960).length < 2 ^ (prefixWord ++ tailWord_1531960).sum := by decide
  have hdescent : baseEnd_1531960 < baseStart_1531960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531965 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1531965 : Nat := 118140960795 + 1531965 * 2 ^ 59
def prefixEnd_1531965 : Nat := 4983230072969 + 3 ^ 40 * 1531965 * 2
def baseEnd_1531965 : Nat := 786634390865203913592127

theorem tailTrace_1531965 : CollatzResearch.WordTrace tailWord_1531965 prefixEnd_1531965 786634390865203913592127 := by
  unfold tailWord_1531965
  simp only [CollatzResearch.WordTrace]
  refine ⟨55875353894959918636981349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37250235929973279091320899 55875353894959918636981349)
  ·
    refine ⟨10476628855304984744434003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55875353894959918636981349 10476628855304984744434003)
    ·
      refine ⟨15714943282957477116651005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10476628855304984744434003 15714943282957477116651005)
      ·
        refine ⟨5893103731109053918744127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15714943282957477116651005 5893103731109053918744127)
        ·
          refine ⟨8839655596663580878116191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893103731109053918744127 8839655596663580878116191)
          ·
            refine ⟨13259483394995371317174287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839655596663580878116191 13259483394995371317174287)
            ·
              refine ⟨19889225092493056975761431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13259483394995371317174287 19889225092493056975761431)
              ·
                refine ⟨29833837638739585463642147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19889225092493056975761431 29833837638739585463642147)
                ·
                  refine ⟨44750756458109378195463221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29833837638739585463642147 44750756458109378195463221)
                  ·
                    refine ⟨4195383417947754205824677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44750756458109378195463221 4195383417947754205824677)
                    ·
                      refine ⟨786634390865203913592127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4195383417947754205824677 786634390865203913592127)
                      ·
                        rfl

theorem cell23_1531965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1531965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531965 prefixEnd_1531965 := by exact prefixLift 1531965
  have htrace : WordTrace (prefixWord ++ tailWord_1531965) baseStart_1531965 baseEnd_1531965 := by
    simpa [prefixWord, tailWord_1531965, baseEnd_1531965] using wordTrace_append hprefix tailTrace_1531965
  have hstable : (prefixWord ++ tailWord_1531965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531965).length < 2 ^ (prefixWord ++ tailWord_1531965).sum := by decide
  have hdescent : baseEnd_1531965 < baseStart_1531965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531969 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1531969 : Nat := 118140960795 + 1531969 * 2 ^ 59
def prefixEnd_1531969 : Nat := 4983230072969 + 3 ^ 40 * 1531969 * 2
def baseEnd_1531969 : Nat := 786636444787821897942109

theorem tailTrace_1531969 : CollatzResearch.WordTrace tailWord_1531969 prefixEnd_1531969 786636444787821897942109 := by
  unfold tailWord_1531969
  simp only [CollatzResearch.WordTrace]
  refine ⟨55875499786945427320126961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37250333191296951546751307 55875499786945427320126961)
  ·
    refine ⟨41906624840209070490095221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55875499786945427320126961 41906624840209070490095221)
    ·
      refine ⟨3928746078769600358446427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41906624840209070490095221 3928746078769600358446427)
      ·
        refine ⟨5893119118154400537669641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928746078769600358446427 5893119118154400537669641)
        ·
          refine ⟨4419839338615800403252231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893119118154400537669641 4419839338615800403252231)
          ·
            refine ⟨6629759007923700604878347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419839338615800403252231 6629759007923700604878347)
            ·
              refine ⟨9944638511885550907317521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629759007923700604878347 9944638511885550907317521)
              ·
                refine ⟨7458478883914163180488141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9944638511885550907317521 7458478883914163180488141)
                ·
                  refine ⟨2796929581467811192683053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7458478883914163180488141 2796929581467811192683053)
                  ·
                    refine ⟨1048848593050429197256145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796929581467811192683053 1048848593050429197256145)
                    ·
                      refine ⟨786636444787821897942109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048848593050429197256145 786636444787821897942109)
                      ·
                        rfl

theorem cell23_1531969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1531969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531969 prefixEnd_1531969 := by exact prefixLift 1531969
  have htrace : WordTrace (prefixWord ++ tailWord_1531969) baseStart_1531969 baseEnd_1531969 := by
    simpa [prefixWord, tailWord_1531969, baseEnd_1531969] using wordTrace_append hprefix tailTrace_1531969
  have hstable : (prefixWord ++ tailWord_1531969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531969).length < 2 ^ (prefixWord ++ tailWord_1531969).sum := by decide
  have hdescent : baseEnd_1531969 < baseStart_1531969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531975 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1531975 : Nat := 118140960795 + 1531975 * 2 ^ 59
def prefixEnd_1531975 : Nat := 4983230072969 + 3 ^ 40 * 1531975 * 2
def baseEnd_1531975 : Nat := 262213175223916291489027

theorem tailTrace_1531975 : CollatzResearch.WordTrace tailWord_1531975 prefixEnd_1531975 262213175223916291489027 := by
  unfold tailWord_1531975
  simp only [CollatzResearch.WordTrace]
  refine ⟨55875718624923690344845379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37250479083282460229896919 55875718624923690344845379)
  ·
    refine ⟨83813577937385535517268069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55875718624923690344845379 83813577937385535517268069)
    ·
      refine ⟨15715045863259787909487763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83813577937385535517268069 15715045863259787909487763)
      ·
        refine ⟨23572568794889681864231645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15715045863259787909487763 23572568794889681864231645)
        ·
          refine ⟨8839713298083630699086867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23572568794889681864231645 8839713298083630699086867)
          ·
            refine ⟨13259569947125446048630301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839713298083630699086867 13259569947125446048630301)
            ·
              refine ⟨4972338730172042268236363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13259569947125446048630301 4972338730172042268236363)
              ·
                refine ⟨7458508095258063402354545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972338730172042268236363 7458508095258063402354545)
                ·
                  refine ⟨5593881071443547551765909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7458508095258063402354545 5593881071443547551765909)
                  ·
                    refine ⟨262213175223916291489027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5593881071443547551765909 262213175223916291489027)
                    ·
                      rfl

theorem cell23_1531975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1531975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531975 prefixEnd_1531975 := by exact prefixLift 1531975
  have htrace : WordTrace (prefixWord ++ tailWord_1531975) baseStart_1531975 baseEnd_1531975 := by
    simpa [prefixWord, tailWord_1531975, baseEnd_1531975] using wordTrace_append hprefix tailTrace_1531975
  have hstable : (prefixWord ++ tailWord_1531975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531975).length < 2 ^ (prefixWord ++ tailWord_1531975).sum := by decide
  have hdescent : baseEnd_1531975 < baseStart_1531975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531985 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_1531985 : Nat := 118140960795 + 1531985 * 2 ^ 59
def prefixEnd_1531985 : Nat := 4983230072969 + 3 ^ 40 * 1531985 * 2
def baseEnd_1531985 : Nat := 786644660478293835342035

theorem tailTrace_1531985 : CollatzResearch.WordTrace tailWord_1531985 prefixEnd_1531985 786644660478293835342035 := by
  unfold tailWord_1531985
  simp only [CollatzResearch.WordTrace]
  refine ⟨55876083354887462052709409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37250722236591641368472939 55876083354887462052709409)
  ·
    refine ⟨41907062516165596539532057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55876083354887462052709409 41907062516165596539532057)
    ·
      refine ⟨31430296887124197404649043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41907062516165596539532057 31430296887124197404649043)
      ·
        refine ⟨47145445330686296106973565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31430296887124197404649043 47145445330686296106973565)
        ·
          refine ⟨17679541999007361040115087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47145445330686296106973565 17679541999007361040115087)
          ·
            refine ⟨26519312998511041560172631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17679541999007361040115087 26519312998511041560172631)
            ·
              refine ⟨39778969497766562340258947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26519312998511041560172631 39778969497766562340258947)
              ·
                refine ⟨59668454246649843510388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39778969497766562340258947 59668454246649843510388421)
                ·
                  refine ⟨11187835171246845658197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59668454246649843510388421 11187835171246845658197829)
                  ·
                    refine ⟨2097719094608783560912093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11187835171246845658197829 2097719094608783560912093)
                    ·
                      refine ⟨786644660478293835342035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097719094608783560912093 786644660478293835342035)
                      ·
                        rfl

theorem cell23_1531985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_1531985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1531985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1531985 prefixEnd_1531985 := by exact prefixLift 1531985
  have htrace : WordTrace (prefixWord ++ tailWord_1531985) baseStart_1531985 baseEnd_1531985 := by
    simpa [prefixWord, tailWord_1531985, baseEnd_1531985] using wordTrace_append hprefix tailTrace_1531985
  have hstable : (prefixWord ++ tailWord_1531985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531985).length < 2 ^ (prefixWord ++ tailWord_1531985).sum := by decide
  have hdescent : baseEnd_1531985 < baseStart_1531985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532016 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2]
def baseStart_1532016 : Nat := 118140960795 + 1532016 * 2 ^ 59
def prefixEnd_1532016 : Nat := 4983230072969 + 3 ^ 40 * 1532016 * 2
def baseEnd_1532016 : Nat := 786660578378583214054393

theorem tailTrace_1532016 : CollatzResearch.WordTrace tailWord_1532016 prefixEnd_1532016 786660578378583214054393 := by
  unfold tailWord_1532016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938607008887577173543951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37251476011850102898058601 27938607008887577173543951)
  ·
    refine ⟨41907910513331365760315927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27938607008887577173543951 41907910513331365760315927)
    ·
      refine ⟨62861865769997048640473891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41907910513331365760315927 62861865769997048640473891)
      ·
        refine ⟨94292798654995572960710837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62861865769997048640473891 94292798654995572960710837)
        ·
          refine ⟨8839949873905834965066641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94292798654995572960710837 8839949873905834965066641)
          ·
            refine ⟨6629962405429376223799981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839949873905834965066641 6629962405429376223799981)
            ·
              refine ⟨2486235902036016083924993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6629962405429376223799981 2486235902036016083924993)
              ·
                refine ⟨1864676926527012062943745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486235902036016083924993 1864676926527012062943745)
                ·
                  refine ⟨1398507694895259047207809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864676926527012062943745 1398507694895259047207809)
                  ·
                    refine ⟨1048880771171444285405857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398507694895259047207809 1048880771171444285405857)
                    ·
                      refine ⟨786660578378583214054393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048880771171444285405857 786660578378583214054393)
                      ·
                        rfl

theorem cell23_1532016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2].length) (baseStart_1532016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532016 prefixEnd_1532016 := by exact prefixLift 1532016
  have htrace : WordTrace (prefixWord ++ tailWord_1532016) baseStart_1532016 baseEnd_1532016 := by
    simpa [prefixWord, tailWord_1532016, baseEnd_1532016] using wordTrace_append hprefix tailTrace_1532016
  have hstable : (prefixWord ++ tailWord_1532016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532016).length < 2 ^ (prefixWord ++ tailWord_1532016).sum := by decide
  have hdescent : baseEnd_1532016 < baseStart_1532016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532022 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1532022 : Nat := 118140960795 + 1532022 * 2 ^ 59
def prefixEnd_1532022 : Nat := 4983230072969 + 3 ^ 40 * 1532022 * 2
def baseEnd_1532022 : Nat := 87407073251390021175485

theorem tailTrace_1532022 : CollatzResearch.WordTrace tailWord_1532022 prefixEnd_1532022 87407073251390021175485 := by
  unfold tailWord_1532022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492339553484588585737895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37251621903835611581204213 3492339553484588585737895)
  ·
    refine ⟨5238509330226882878606843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492339553484588585737895 5238509330226882878606843)
    ·
      refine ⟨7857763995340324317910265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238509330226882878606843 7857763995340324317910265)
      ·
        refine ⟨5893322996505243238432699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7857763995340324317910265 5893322996505243238432699)
        ·
          refine ⟨8839984494757864857649049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893322996505243238432699 8839984494757864857649049)
          ·
            refine ⟨6629988371068398643236787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839984494757864857649049 6629988371068398643236787)
            ·
              refine ⟨9944982556602597964855181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629988371068398643236787 9944982556602597964855181)
              ·
                refine ⟨3729368458725974236820693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9944982556602597964855181 3729368458725974236820693)
                ·
                  refine ⟨87407073251390021175485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3729368458725974236820693 87407073251390021175485)
                  ·
                    rfl

theorem cell23_1532022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1532022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532022 prefixEnd_1532022 := by exact prefixLift 1532022
  have htrace : WordTrace (prefixWord ++ tailWord_1532022) baseStart_1532022 baseEnd_1532022 := by
    simpa [prefixWord, tailWord_1532022, baseEnd_1532022] using wordTrace_append hprefix tailTrace_1532022
  have hstable : (prefixWord ++ tailWord_1532022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532022).length < 2 ^ (prefixWord ++ tailWord_1532022).sum := by decide
  have hdescent : baseEnd_1532022 < baseStart_1532022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532033 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_1532033 : Nat := 118140960795 + 1532033 * 2 ^ 59
def prefixEnd_1532033 : Nat := 4983230072969 + 3 ^ 40 * 1532033 * 2
def baseEnd_1532033 : Nat := 786669307549709647541815

theorem tailTrace_1532033 : CollatzResearch.WordTrace tailWord_1532033 prefixEnd_1532033 786669307549709647541815 := by
  unfold tailWord_1532033
  simp only [CollatzResearch.WordTrace]
  refine ⟨55877834058713566250456753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37251889372475710833637835 55877834058713566250456753)
  ·
    refine ⟨41908375544035174687842565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55877834058713566250456753 41908375544035174687842565)
    ·
      refine ⟨7857820414506595253970481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41908375544035174687842565 7857820414506595253970481)
      ·
        refine ⟨5893365310879946440477861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7857820414506595253970481 5893365310879946440477861)
        ·
          refine ⟨1105005995789989957589599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5893365310879946440477861 1105005995789989957589599)
          ·
            refine ⟨1657508993684984936384399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105005995789989957589599 1657508993684984936384399)
            ·
              refine ⟨2486263490527477404576599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657508993684984936384399 2486263490527477404576599)
              ·
                refine ⟨3729395235791216106864899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486263490527477404576599 3729395235791216106864899)
                ·
                  refine ⟨5594092853686824160297349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729395235791216106864899 5594092853686824160297349)
                  ·
                    refine ⟨1048892410066279530055753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594092853686824160297349 1048892410066279530055753)
                    ·
                      refine ⟨786669307549709647541815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1048892410066279530055753 786669307549709647541815)
                      ·
                        rfl

theorem cell23_1532033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_1532033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532033 prefixEnd_1532033 := by exact prefixLift 1532033
  have htrace : WordTrace (prefixWord ++ tailWord_1532033) baseStart_1532033 baseEnd_1532033 := by
    simpa [prefixWord, tailWord_1532033, baseEnd_1532033] using wordTrace_append hprefix tailTrace_1532033
  have hstable : (prefixWord ++ tailWord_1532033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532033).length < 2 ^ (prefixWord ++ tailWord_1532033).sum := by decide
  have hdescent : baseEnd_1532033 < baseStart_1532033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532035 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 7]
def baseStart_1532035 : Nat := 118140960795 + 1532035 * 2 ^ 59
def prefixEnd_1532035 : Nat := 4983230072969 + 3 ^ 40 * 1532035 * 2
def baseEnd_1532035 : Nat := 262223444837006213238935

theorem tailTrace_1532035 : CollatzResearch.WordTrace tailWord_1532035 prefixEnd_1532035 262223444837006213238935 := by
  unfold tailWord_1532035
  simp only [CollatzResearch.WordTrace]
  refine ⟨55877907004706320592029559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37251938003137547061353039 55877907004706320592029559)
  ·
    refine ⟨83816860507059480888044339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55877907004706320592029559 83816860507059480888044339)
    ·
      refine ⟨125725290760589221332066509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83816860507059480888044339 125725290760589221332066509)
      ·
        refine ⟨47146984035220957999524941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125725290760589221332066509 47146984035220957999524941)
        ·
          refine ⟨17680119013207859249821853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47146984035220957999524941 17680119013207859249821853)
          ·
            refine ⟨6630044629952947218683195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17680119013207859249821853 6630044629952947218683195)
            ·
              refine ⟨9945066944929420828024793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630044629952947218683195 9945066944929420828024793)
              ·
                refine ⟨7458800208697065621018595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9945066944929420828024793 7458800208697065621018595)
                ·
                  refine ⟨11188200313045598431527893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458800208697065621018595 11188200313045598431527893)
                  ·
                    refine ⟨262223444837006213238935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11188200313045598431527893 262223444837006213238935)
                    ·
                      rfl

theorem cell23_1532035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_1532035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532035 prefixEnd_1532035 := by exact prefixLift 1532035
  have htrace : WordTrace (prefixWord ++ tailWord_1532035) baseStart_1532035 baseEnd_1532035 := by
    simpa [prefixWord, tailWord_1532035, baseEnd_1532035] using wordTrace_append hprefix tailTrace_1532035
  have hstable : (prefixWord ++ tailWord_1532035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532035).length < 2 ^ (prefixWord ++ tailWord_1532035).sum := by decide
  have hdescent : baseEnd_1532035 < baseStart_1532035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532056 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 5]
def baseStart_1532056 : Nat := 118140960795 + 1532056 * 2 ^ 59
def prefixEnd_1532056 : Nat := 4983230072969 + 3 ^ 40 * 1532056 * 2
def baseEnd_1532056 : Nat := 87409013067195895283801

theorem tailTrace_1532056 : CollatzResearch.WordTrace tailWord_1532056 prefixEnd_1532056 87409013067195895283801 := by
  unfold tailWord_1532056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27939336468815120589272011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37252448625086827452362681 27939336468815120589272011)
  ·
    refine ⟨41909004703222680883908017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27939336468815120589272011 41909004703222680883908017)
    ·
      refine ⟨31431753527417010662931013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41909004703222680883908017 31431753527417010662931013)
      ·
        refine ⟨5893453786390689499299565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31431753527417010662931013 5893453786390689499299565)
        ·
          refine ⟨2210045169896508562237337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5893453786390689499299565 2210045169896508562237337)
          ·
            refine ⟨1657533877422381421678003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210045169896508562237337 1657533877422381421678003)
            ·
              refine ⟨2486300816133572132517005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657533877422381421678003 2486300816133572132517005)
              ·
                refine ⟨932362806050089549693877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486300816133572132517005 932362806050089549693877)
                ·
                  refine ⟨87409013067195895283801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932362806050089549693877 87409013067195895283801)
                  ·
                    rfl

theorem cell23_1532056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 5].length) (baseStart_1532056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532056 prefixEnd_1532056 := by exact prefixLift 1532056
  have htrace : WordTrace (prefixWord ++ tailWord_1532056) baseStart_1532056 baseEnd_1532056 := by
    simpa [prefixWord, tailWord_1532056, baseEnd_1532056] using wordTrace_append hprefix tailTrace_1532056
  have hstable : (prefixWord ++ tailWord_1532056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532056).length < 2 ^ (prefixWord ++ tailWord_1532056).sum := by decide
  have hdescent : baseEnd_1532056 < baseStart_1532056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532133 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1532133 : Nat := 118140960795 + 1532133 * 2 ^ 59
def prefixEnd_1532133 : Nat := 4983230072969 + 3 ^ 40 * 1532133 * 2
def baseEnd_1532133 : Nat := 262240218538386418763785

theorem tailTrace_1532133 : CollatzResearch.WordTrace tailWord_1532133 prefixEnd_1532133 262240218538386418763785 := by
  unfold tailWord_1532133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55881481358351283329097053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37254320905567522219398035 55881481358351283329097053)
  ·
    refine ⟨20955555509381731248411395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55881481358351283329097053 20955555509381731248411395)
    ·
      refine ⟨31433333264072596872617093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20955555509381731248411395 31433333264072596872617093)
      ·
        refine ⟨5893749987013611913615705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31433333264072596872617093 5893749987013611913615705)
        ·
          refine ⟨4420312490260208935211779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893749987013611913615705 4420312490260208935211779)
          ·
            refine ⟨6630468735390313402817669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420312490260208935211779 6630468735390313402817669)
            ·
              refine ⟨1243212887885683763028313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6630468735390313402817669 1243212887885683763028313)
              ·
                refine ⟨932409665914262822271235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243212887885683763028313 932409665914262822271235)
                ·
                  refine ⟨1398614498871394233406853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932409665914262822271235 1398614498871394233406853)
                  ·
                    refine ⟨262240218538386418763785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398614498871394233406853 262240218538386418763785)
                    ·
                      rfl

theorem cell23_1532133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1532133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532133 prefixEnd_1532133 := by exact prefixLift 1532133
  have htrace : WordTrace (prefixWord ++ tailWord_1532133) baseStart_1532133 baseEnd_1532133 := by
    simpa [prefixWord, tailWord_1532133, baseEnd_1532133] using wordTrace_append hprefix tailTrace_1532133
  have hstable : (prefixWord ++ tailWord_1532133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532133).length < 2 ^ (prefixWord ++ tailWord_1532133).sum := by decide
  have hdescent : baseEnd_1532133 < baseStart_1532133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532139 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 3]
def baseStart_1532139 : Nat := 118140960795 + 1532139 * 2 ^ 59
def prefixEnd_1532139 : Nat := 4983230072969 + 3 ^ 40 * 1532139 * 2
def baseEnd_1532139 : Nat := 786723736499086232816327

theorem tailTrace_1532139 : CollatzResearch.WordTrace tailWord_1532139 prefixEnd_1532139 786723736499086232816327 := by
  unfold tailWord_1532139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55881700196329546353815471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37254466797553030902543647 55881700196329546353815471)
  ·
    refine ⟨83822550294494319530723207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55881700196329546353815471 83822550294494319530723207)
    ·
      refine ⟨125733825441741479296084811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83822550294494319530723207 125733825441741479296084811)
      ·
        refine ⟨188600738162612218944127217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125733825441741479296084811 188600738162612218944127217)
        ·
          refine ⟨141450553621959164208095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188600738162612218944127217 141450553621959164208095413)
          ·
            refine ⟨13260989402058671644508945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141450553621959164208095413 13260989402058671644508945)
            ·
              refine ⟨9945742051544003733381709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13260989402058671644508945 9945742051544003733381709)
              ·
                refine ⟨3729653269329001400018141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9945742051544003733381709 3729653269329001400018141)
                ·
                  refine ⟨1398619975998375525006803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729653269329001400018141 1398619975998375525006803)
                  ·
                    refine ⟨2097929963997563287510205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398619975998375525006803 2097929963997563287510205)
                    ·
                      refine ⟨786723736499086232816327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097929963997563287510205 786723736499086232816327)
                      ·
                        rfl

theorem cell23_1532139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 3].length) (baseStart_1532139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532139 prefixEnd_1532139 := by exact prefixLift 1532139
  have htrace : WordTrace (prefixWord ++ tailWord_1532139) baseStart_1532139 baseEnd_1532139 := by
    simpa [prefixWord, tailWord_1532139, baseEnd_1532139] using wordTrace_append hprefix tailTrace_1532139
  have hstable : (prefixWord ++ tailWord_1532139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532139).length < 2 ^ (prefixWord ++ tailWord_1532139).sum := by decide
  have hdescent : baseEnd_1532139 < baseStart_1532139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532156 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_1532156 : Nat := 118140960795 + 1532156 * 2 ^ 59
def prefixEnd_1532156 : Nat := 4983230072969 + 3 ^ 40 * 1532156 * 2
def baseEnd_1532156 : Nat := 786732465670212666303749

theorem tailTrace_1532156 : CollatzResearch.WordTrace tailWord_1532156 prefixEnd_1532156 786732465670212666303749 := by
  unfold tailWord_1532156
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941160118633979128592161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37254880158178638838122881 27941160118633979128592161)
  ·
    refine ⟨20955870088975484346444121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27941160118633979128592161 20955870088975484346444121)
    ·
      refine ⟨15716902566731613259833091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20955870088975484346444121 15716902566731613259833091)
      ·
        refine ⟨23575353850097419889749637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716902566731613259833091 23575353850097419889749637)
        ·
          refine ⟨4420378846893266229328057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23575353850097419889749637 4420378846893266229328057)
          ·
            refine ⟨3315284135169949671996043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420378846893266229328057 3315284135169949671996043)
            ·
              refine ⟨4972926202754924507994065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315284135169949671996043 4972926202754924507994065)
              ·
                refine ⟨3729694652066193380995549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972926202754924507994065 3729694652066193380995549)
                ·
                  refine ⟨1398635494524822517873331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729694652066193380995549 1398635494524822517873331)
                  ·
                    refine ⟨2097953241787233776809997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398635494524822517873331 2097953241787233776809997)
                    ·
                      refine ⟨786732465670212666303749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097953241787233776809997 786732465670212666303749)
                      ·
                        rfl

theorem cell23_1532156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_1532156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532156 prefixEnd_1532156 := by exact prefixLift 1532156
  have htrace : WordTrace (prefixWord ++ tailWord_1532156) baseStart_1532156 baseEnd_1532156 := by
    simpa [prefixWord, tailWord_1532156, baseEnd_1532156] using wordTrace_append hprefix tailTrace_1532156
  have hstable : (prefixWord ++ tailWord_1532156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532156).length < 2 ^ (prefixWord ++ tailWord_1532156).sum := by decide
  have hdescent : baseEnd_1532156 < baseStart_1532156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532172 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_1532172 : Nat := 118140960795 + 1532172 * 2 ^ 59
def prefixEnd_1532172 : Nat := 4983230072969 + 3 ^ 40 * 1532172 * 2
def baseEnd_1532172 : Nat := 262246893786894867901225

theorem tailTrace_1532172 : CollatzResearch.WordTrace tailWord_1532172 prefixEnd_1532172 262246893786894867901225 := by
  unfold tailWord_1532172
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941451902604996494883385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37255269203473328659844513 27941451902604996494883385)
  ·
    refine ⟨20956088926953747371162539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27941451902604996494883385 20956088926953747371162539)
    ·
      refine ⟨31434133390430621056743809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20956088926953747371162539 31434133390430621056743809)
      ·
        refine ⟨23575600042822965792557857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31434133390430621056743809 23575600042822965792557857)
        ·
          refine ⟨17681700032117224344418393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23575600042822965792557857 17681700032117224344418393)
          ·
            refine ⟨13261275024087918258313795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681700032117224344418393 13261275024087918258313795)
            ·
              refine ⟨19891912536131877387470693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13261275024087918258313795 19891912536131877387470693)
              ·
                refine ⟨3729733600524727010150755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19891912536131877387470693 3729733600524727010150755)
                ·
                  refine ⟨5594600400787090515226133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729733600524727010150755 5594600400787090515226133)
                  ·
                    refine ⟨262246893786894867901225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5594600400787090515226133 262246893786894867901225)
                    ·
                      rfl

theorem cell23_1532172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_1532172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532172 prefixEnd_1532172 := by exact prefixLift 1532172
  have htrace : WordTrace (prefixWord ++ tailWord_1532172) baseStart_1532172 baseEnd_1532172 := by
    simpa [prefixWord, tailWord_1532172, baseEnd_1532172] using wordTrace_append hprefix tailTrace_1532172
  have hstable : (prefixWord ++ tailWord_1532172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532172).length < 2 ^ (prefixWord ++ tailWord_1532172).sum := by decide
  have hdescent : baseEnd_1532172 < baseStart_1532172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532190 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1532190 : Nat := 118140960795 + 1532190 * 2 ^ 59
def prefixEnd_1532190 : Nat := 4983230072969 + 3 ^ 40 * 1532190 * 2
def baseEnd_1532190 : Nat := 786749924012465533278593

theorem tailTrace_1532190 : CollatzResearch.WordTrace tailWord_1532190 prefixEnd_1532190 786749924012465533278593 := by
  unfold tailWord_1532190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985445039893097757990253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37255706879429854709281349 6985445039893097757990253)
  ·
    refine ⟨2619541889959911659246345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6985445039893097757990253 2619541889959911659246345)
    ·
      refine ⟨1964656417469933744434759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2619541889959911659246345 1964656417469933744434759)
      ·
        refine ⟨2946984626204900616652139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964656417469933744434759 2946984626204900616652139)
        ·
          refine ⟨4420476939307350924978209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946984626204900616652139 4420476939307350924978209)
          ·
            refine ⟨3315357704480513193733657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420476939307350924978209 3315357704480513193733657)
            ·
              refine ⟨2486518278360384895300243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315357704480513193733657 2486518278360384895300243)
              ·
                refine ⟨3729777417540577342950365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486518278360384895300243 3729777417540577342950365)
                ·
                  refine ⟨1398666531577716503606387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729777417540577342950365 1398666531577716503606387)
                  ·
                    refine ⟨2097999797366574755409581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398666531577716503606387 2097999797366574755409581)
                    ·
                      refine ⟨786749924012465533278593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2097999797366574755409581 786749924012465533278593)
                      ·
                        rfl

theorem cell23_1532190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1532190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532190 prefixEnd_1532190 := by exact prefixLift 1532190
  have htrace : WordTrace (prefixWord ++ tailWord_1532190) baseStart_1532190 baseEnd_1532190 := by
    simpa [prefixWord, tailWord_1532190, baseEnd_1532190] using wordTrace_append hprefix tailTrace_1532190
  have hstable : (prefixWord ++ tailWord_1532190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532190).length < 2 ^ (prefixWord ++ tailWord_1532190).sum := by decide
  have hdescent : baseEnd_1532190 < baseStart_1532190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
