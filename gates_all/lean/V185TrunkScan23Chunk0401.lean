import V185TrunkScan23Chunk0400

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2371118 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2371118 : Nat := 118140960795 + 2371118 * 2 ^ 59
def prefixEnd_2371118 : Nat := 4983230072969 + 3 ^ 40 * 2371118 * 2
def baseEnd_2371118 : Nat := 1217523222527559223620433

theorem tailTrace_2371118 : CollatzResearch.WordTrace tailWord_2371118 prefixEnd_2371118 1217523222527559223620433 := by
  unfold tailWord_2371118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810222277981489444927251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57654518815901277039612005 10810222277981489444927251)
  ·
    refine ⟨16215333416972234167390877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810222277981489444927251 16215333416972234167390877)
    ·
      refine ⟨6080750031364587812771579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16215333416972234167390877 6080750031364587812771579)
      ·
        refine ⟨9121125047046881719157369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080750031364587812771579 9121125047046881719157369)
        ·
          refine ⟨6840843785285161289368027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9121125047046881719157369 6840843785285161289368027)
          ·
            refine ⟨10261265677927741934052041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840843785285161289368027 10261265677927741934052041)
            ·
              refine ⟨7695949258445806450539031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10261265677927741934052041 7695949258445806450539031)
              ·
                refine ⟨11543923887668709675808547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695949258445806450539031 11543923887668709675808547)
                ·
                  refine ⟨17315885831503064513712821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11543923887668709675808547 17315885831503064513712821)
                  ·
                    refine ⟨1623364296703412298160577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17315885831503064513712821 1623364296703412298160577)
                    ·
                      refine ⟨1217523222527559223620433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623364296703412298160577 1217523222527559223620433)
                      ·
                        rfl

theorem cell23_2371118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2371118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371118 prefixEnd_2371118 := by exact prefixLift 2371118
  have htrace : WordTrace (prefixWord ++ tailWord_2371118) baseStart_2371118 baseEnd_2371118 := by
    simpa [prefixWord, tailWord_2371118, baseEnd_2371118] using wordTrace_append hprefix tailTrace_2371118
  have hstable : (prefixWord ++ tailWord_2371118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371118).length < 2 ^ (prefixWord ++ tailWord_2371118).sum := by decide
  have hdescent : baseEnd_2371118 < baseStart_2371118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371125 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2371125 : Nat := 118140960795 + 2371125 * 2 ^ 59
def prefixEnd_2371125 : Nat := 4983230072969 + 3 ^ 40 * 2371125 * 2
def baseEnd_2371125 : Nat := 1217526816892140696232901

theorem tailTrace_2371125 : CollatzResearch.WordTrace tailWord_2371125 prefixEnd_2371125 1217526816892140696232901 := by
  unfold tailWord_2371125
  simp only [CollatzResearch.WordTrace]
  refine ⟨86482033534826555754922829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57654689023217703836615219 86482033534826555754922829)
  ·
    refine ⟨32430762575559958408096061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86482033534826555754922829 32430762575559958408096061)
    ·
      refine ⟨12161535965834984403036023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32430762575559958408096061 12161535965834984403036023)
      ·
        refine ⟨18242303948752476604554035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161535965834984403036023 18242303948752476604554035)
        ·
          refine ⟨27363455923128714906831053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18242303948752476604554035 27363455923128714906831053)
          ·
            refine ⟨10261295971173268090061645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27363455923128714906831053 10261295971173268090061645)
            ·
              refine ⟨3847985989189975533773117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261295971173268090061645 3847985989189975533773117)
              ·
                refine ⟨1442994745946240825164919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3847985989189975533773117 1442994745946240825164919)
                ·
                  refine ⟨2164492118919361237747379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442994745946240825164919 2164492118919361237747379)
                  ·
                    refine ⟨3246738178379041856621069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164492118919361237747379 3246738178379041856621069)
                    ·
                      refine ⟨1217526816892140696232901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246738178379041856621069 1217526816892140696232901)
                      ·
                        rfl

theorem cell23_2371125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2371125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371125 prefixEnd_2371125 := by exact prefixLift 2371125
  have htrace : WordTrace (prefixWord ++ tailWord_2371125) baseStart_2371125 baseEnd_2371125 := by
    simpa [prefixWord, tailWord_2371125, baseEnd_2371125] using wordTrace_append hprefix tailTrace_2371125
  have hstable : (prefixWord ++ tailWord_2371125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371125).length < 2 ^ (prefixWord ++ tailWord_2371125).sum := by decide
  have hdescent : baseEnd_2371125 < baseStart_2371125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371141 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_2371141 : Nat := 118140960795 + 2371141 * 2 ^ 59
def prefixEnd_2371141 : Nat := 4983230072969 + 3 ^ 40 * 2371141 * 2
def baseEnd_2371141 : Nat := 405845010860870877877609

theorem tailTrace_2371141 : CollatzResearch.WordTrace tailWord_2371141 prefixEnd_2371141 405845010860870877877609 := by
  unfold tailWord_2371141
  simp only [CollatzResearch.WordTrace]
  refine ⟨86482617102768590487505277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57655078068512393658336851 86482617102768590487505277)
  ·
    refine ⟨32430981413538221432814479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86482617102768590487505277 32430981413538221432814479)
    ·
      refine ⟨48646472120307332149221719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32430981413538221432814479 48646472120307332149221719)
      ·
        refine ⟨72969708180460998223832579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48646472120307332149221719 72969708180460998223832579)
        ·
          refine ⟨109454562270691497335748869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72969708180460998223832579 109454562270691497335748869)
          ·
            refine ⟨20522730425754655750452913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109454562270691497335748869 20522730425754655750452913)
            ·
              refine ⟨15392047819315991812839685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20522730425754655750452913 15392047819315991812839685)
              ·
                refine ⟨2886008966121748464907441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15392047819315991812839685 2886008966121748464907441)
                ·
                  refine ⟨2164506724591311348680581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886008966121748464907441 2164506724591311348680581)
                  ·
                    refine ⟨405845010860870877877609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164506724591311348680581 405845010860870877877609)
                    ·
                      rfl

theorem cell23_2371141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_2371141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371141 prefixEnd_2371141 := by exact prefixLift 2371141
  have htrace : WordTrace (prefixWord ++ tailWord_2371141) baseStart_2371141 baseEnd_2371141 := by
    simpa [prefixWord, tailWord_2371141, baseEnd_2371141] using wordTrace_append hprefix tailTrace_2371141
  have hstable : (prefixWord ++ tailWord_2371141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371141).length < 2 ^ (prefixWord ++ tailWord_2371141).sum := by decide
  have hdescent : baseEnd_2371141 < baseStart_2371141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371154 : List Nat := [3, 2, 2, 1, 2, 2, 1, 10]
def baseStart_2371154 : Nat := 118140960795 + 2371154 * 2 ^ 59
def prefixEnd_2371154 : Nat := 4983230072969 + 3 ^ 40 * 2371154 * 2
def baseEnd_2371154 : Nat := 45094137327078558621121

theorem tailTrace_2371154 : CollatzResearch.WordTrace tailWord_2371154 prefixEnd_2371154 45094137327078558621121 := by
  unfold tailWord_2371154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620772812930373426932129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57655394167814329138485677 21620772812930373426932129)
  ·
    refine ⟨16215579609697780070199097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21620772812930373426932129 16215579609697780070199097)
    ·
      refine ⟨12161684707273335052649323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215579609697780070199097 12161684707273335052649323)
      ·
        refine ⟨18242527060910002578973985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161684707273335052649323 18242527060910002578973985)
        ·
          refine ⟨13681895295682501934230489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18242527060910002578973985 13681895295682501934230489)
          ·
            refine ⟨10261421471761876450672867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13681895295682501934230489 10261421471761876450672867)
            ·
              refine ⟨15392132207642814676009301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261421471761876450672867 15392132207642814676009301)
              ·
                refine ⟨45094137327078558621121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15392132207642814676009301 45094137327078558621121)
                ·
                  rfl

theorem cell23_2371154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_2371154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371154 prefixEnd_2371154 := by exact prefixLift 2371154
  have htrace : WordTrace (prefixWord ++ tailWord_2371154) baseStart_2371154 baseEnd_2371154 := by
    simpa [prefixWord, tailWord_2371154, baseEnd_2371154] using wordTrace_append hprefix tailTrace_2371154
  have hstable : (prefixWord ++ tailWord_2371154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371154).length < 2 ^ (prefixWord ++ tailWord_2371154).sum := by decide
  have hdescent : baseEnd_2371154 < baseStart_2371154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371165 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2371165 : Nat := 118140960795 + 2371165 * 2 ^ 59
def prefixEnd_2371165 : Nat := 4983230072969 + 3 ^ 40 * 2371165 * 2
def baseEnd_2371165 : Nat := 1217547356118320539732717

theorem tailTrace_2371165 : CollatzResearch.WordTrace tailWord_2371165 prefixEnd_2371165 1217547356118320539732717 := by
  unfold tailWord_2371165
  simp only [CollatzResearch.WordTrace]
  refine ⟨86483492454681642586378949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57655661636454428390919299 86483492454681642586378949)
  ·
    refine ⟨16215654835252807984946053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86483492454681642586378949 16215654835252807984946053)
    ·
      refine ⟨3040435281609901497177385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16215654835252807984946053 3040435281609901497177385)
      ·
        refine ⟨2280326461207426122883039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3040435281609901497177385 2280326461207426122883039)
        ·
          refine ⟨3420489691811139184324559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280326461207426122883039 3420489691811139184324559)
          ·
            refine ⟨5130734537716708776486839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420489691811139184324559 5130734537716708776486839)
            ·
              refine ⟨7696101806575063164730259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130734537716708776486839 7696101806575063164730259)
              ·
                refine ⟨11544152709862594747095389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696101806575063164730259 11544152709862594747095389)
                ·
                  refine ⟨4329057266198473030160771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11544152709862594747095389 4329057266198473030160771)
                  ·
                    refine ⟨6493585899297709545241157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329057266198473030160771 6493585899297709545241157)
                    ·
                      refine ⟨1217547356118320539732717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6493585899297709545241157 1217547356118320539732717)
                      ·
                        rfl

theorem cell23_2371165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2371165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371165 prefixEnd_2371165 := by exact prefixLift 2371165
  have htrace : WordTrace (prefixWord ++ tailWord_2371165) baseStart_2371165 baseEnd_2371165 := by
    simpa [prefixWord, tailWord_2371165, baseEnd_2371165] using wordTrace_append hprefix tailTrace_2371165
  have hstable : (prefixWord ++ tailWord_2371165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371165).length < 2 ^ (prefixWord ++ tailWord_2371165).sum := by decide
  have hdescent : baseEnd_2371165 < baseStart_2371165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371255 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_2371255 : Nat := 118140960795 + 2371255 * 2 ^ 59
def prefixEnd_2371255 : Nat := 4983230072969 + 3 ^ 40 * 2371255 * 2
def baseEnd_2371255 : Nat := 1217593569377225187607303

theorem tailTrace_2371255 : CollatzResearch.WordTrace tailWord_2371255 prefixEnd_2371255 1217593569377225187607303 := by
  unfold tailWord_2371255
  simp only [CollatzResearch.WordTrace]
  refine ⟨86486775024355587957155219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57657850016237058638103479 86486775024355587957155219)
  ·
    refine ⟨129730162536533381935732829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86486775024355587957155219 129730162536533381935732829)
    ·
      refine ⟨48648810951200018225899811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129730162536533381935732829 48648810951200018225899811)
      ·
        refine ⟨72973216426800027338849717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48648810951200018225899811 72973216426800027338849717)
        ·
          refine ⟨6841239040012502563017161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72973216426800027338849717 6841239040012502563017161)
          ·
            refine ⟨5130929280009376922262871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6841239040012502563017161 5130929280009376922262871)
            ·
              refine ⟨7696393920014065383394307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130929280009376922262871 7696393920014065383394307)
              ·
                refine ⟨11544590880021098075091461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696393920014065383394307 11544590880021098075091461)
                ·
                  refine ⟨2164610790003955889079649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11544590880021098075091461 2164610790003955889079649)
                  ·
                    refine ⟨1623458092502966916809737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164610790003955889079649 1623458092502966916809737)
                    ·
                      refine ⟨1217593569377225187607303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623458092502966916809737 1217593569377225187607303)
                      ·
                        rfl

theorem cell23_2371255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_2371255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371255 prefixEnd_2371255 := by exact prefixLift 2371255
  have htrace : WordTrace (prefixWord ++ tailWord_2371255) baseStart_2371255 baseEnd_2371255 := by
    simpa [prefixWord, tailWord_2371255, baseEnd_2371255] using wordTrace_append hprefix tailTrace_2371255
  have hstable : (prefixWord ++ tailWord_2371255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371255).length < 2 ^ (prefixWord ++ tailWord_2371255).sum := by decide
  have hdescent : baseEnd_2371255 < baseStart_2371255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371261 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 7]
def baseStart_2371261 : Nat := 118140960795 + 2371261 * 2 ^ 59
def prefixEnd_2371261 : Nat := 4983230072969 + 3 ^ 40 * 2371261 * 2
def baseEnd_2371261 : Nat := 135288516695683573792475

theorem tailTrace_2371261 : CollatzResearch.WordTrace tailWord_2371261 prefixEnd_2371261 135288516695683573792475 := by
  unfold tailWord_2371261
  simp only [CollatzResearch.WordTrace]
  refine ⟨86486993862333850981873637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57657995908222567321249091 86486993862333850981873637)
  ·
    refine ⟨16216311349187597059101307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86486993862333850981873637 16216311349187597059101307)
    ·
      refine ⟨24324467023781395588651961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216311349187597059101307 24324467023781395588651961)
      ·
        refine ⟨18243350267836046691488971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24324467023781395588651961 18243350267836046691488971)
        ·
          refine ⟨27365025401754070037233457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243350267836046691488971 27365025401754070037233457)
          ·
            refine ⟨20523769051315552527925093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27365025401754070037233457 20523769051315552527925093)
            ·
              refine ⟨3848206697121666098985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20523769051315552527925093 3848206697121666098985955)
              ·
                refine ⟨5772310045682499148478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848206697121666098985955 5772310045682499148478933)
                ·
                  refine ⟨135288516695683573792475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5772310045682499148478933 135288516695683573792475)
                  ·
                    rfl

theorem cell23_2371261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_2371261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371261 prefixEnd_2371261 := by exact prefixLift 2371261
  have htrace : WordTrace (prefixWord ++ tailWord_2371261) baseStart_2371261 baseEnd_2371261 := by
    simpa [prefixWord, tailWord_2371261, baseEnd_2371261] using wordTrace_append hprefix tailTrace_2371261
  have hstable : (prefixWord ++ tailWord_2371261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371261).length < 2 ^ (prefixWord ++ tailWord_2371261).sum := by decide
  have hdescent : baseEnd_2371261 < baseStart_2371261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371266 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2371266 : Nat := 118140960795 + 2371266 * 2 ^ 59
def prefixEnd_2371266 : Nat := 4983230072969 + 3 ^ 40 * 2371266 * 2
def baseEnd_2371266 : Nat := 1217599217664424644569753

theorem tailTrace_2371266 : CollatzResearch.WordTrace tailWord_2371266 prefixEnd_2371266 1217599217664424644569753 := by
  unfold tailWord_2371266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621794056828934208951413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57658117484877157890537101 21621794056828934208951413)
  ·
    refine ⟨2027043192827712582089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21621794056828934208951413 2027043192827712582089195)
    ·
      refine ⟨3040564789241568873133793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027043192827712582089195 3040564789241568873133793)
      ·
        refine ⟨2280423591931176654850345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3040564789241568873133793 2280423591931176654850345)
        ·
          refine ⟨1710317693948382491137759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280423591931176654850345 1710317693948382491137759)
          ·
            refine ⟨2565476540922573736706639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710317693948382491137759 2565476540922573736706639)
            ·
              refine ⟨3848214811383860605059959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565476540922573736706639 3848214811383860605059959)
              ·
                refine ⟨5772322217075790907589939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848214811383860605059959 5772322217075790907589939)
                ·
                  refine ⟨8658483325613686361384909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5772322217075790907589939 8658483325613686361384909)
                  ·
                    refine ⟨3246931247105132385519341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8658483325613686361384909 3246931247105132385519341)
                    ·
                      refine ⟨1217599217664424644569753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246931247105132385519341 1217599217664424644569753)
                      ·
                        rfl

theorem cell23_2371266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2371266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371266 prefixEnd_2371266 := by exact prefixLift 2371266
  have htrace : WordTrace (prefixWord ++ tailWord_2371266) baseStart_2371266 baseEnd_2371266 := by
    simpa [prefixWord, tailWord_2371266, baseEnd_2371266] using wordTrace_append hprefix tailTrace_2371266
  have hstable : (prefixWord ++ tailWord_2371266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371266).length < 2 ^ (prefixWord ++ tailWord_2371266).sum := by decide
  have hdescent : baseEnd_2371266 < baseStart_2371266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371271 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2371271 : Nat := 118140960795 + 2371271 * 2 ^ 59
def prefixEnd_2371271 : Nat := 4983230072969 + 3 ^ 40 * 2371271 * 2
def baseEnd_2371271 : Nat := 1217601785067697125007229

theorem tailTrace_2371271 : CollatzResearch.WordTrace tailWord_2371271 prefixEnd_2371271 1217601785067697125007229 := by
  unfold tailWord_2371271
  simp only [CollatzResearch.WordTrace]
  refine ⟨86487358592297622689737667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57658239061531748459825111 86487358592297622689737667)
  ·
    refine ⟨129731037888446434034606501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86487358592297622689737667 129731037888446434034606501)
    ·
      refine ⟨24324569604083706381488719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129731037888446434034606501 24324569604083706381488719)
      ·
        refine ⟨36486854406125559572233079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24324569604083706381488719 36486854406125559572233079)
        ·
          refine ⟨54730281609188339358349619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36486854406125559572233079 54730281609188339358349619)
          ·
            refine ⟨82095422413782509037524429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54730281609188339358349619 82095422413782509037524429)
            ·
              refine ⟨30785783405168440889071661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82095422413782509037524429 30785783405168440889071661)
              ·
                refine ⟨11544668776938165333401873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30785783405168440889071661 11544668776938165333401873)
                ·
                  refine ⟨8658501582703624000051405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11544668776938165333401873 8658501582703624000051405)
                  ·
                    refine ⟨3246938093513859000019277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8658501582703624000051405 3246938093513859000019277)
                    ·
                      refine ⟨1217601785067697125007229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246938093513859000019277 1217601785067697125007229)
                      ·
                        rfl

theorem cell23_2371271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2371271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371271 prefixEnd_2371271 := by exact prefixLift 2371271
  have htrace : WordTrace (prefixWord ++ tailWord_2371271) baseStart_2371271 baseEnd_2371271 := by
    simpa [prefixWord, tailWord_2371271, baseEnd_2371271] using wordTrace_append hprefix tailTrace_2371271
  have hstable : (prefixWord ++ tailWord_2371271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371271).length < 2 ^ (prefixWord ++ tailWord_2371271).sum := by decide
  have hdescent : baseEnd_2371271 < baseStart_2371271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371272 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_2371272 : Nat := 118140960795 + 2371272 * 2 ^ 59
def prefixEnd_2371272 : Nat := 4983230072969 + 3 ^ 40 * 2371272 * 2
def baseEnd_2371272 : Nat := 1217602298548351621094725

theorem tailTrace_2371272 : CollatzResearch.WordTrace tailWord_2371272 prefixEnd_2371272 1217602298548351621094725 := by
  unfold tailWord_2371272
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243697532646999930262035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57658263376862666573682713 43243697532646999930262035)
  ·
    refine ⟨64865546298970499895393053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43243697532646999930262035 64865546298970499895393053)
    ·
      refine ⟨24324579862113937460772395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64865546298970499895393053 24324579862113937460772395)
      ·
        refine ⟨36486869793170906191158593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24324579862113937460772395 36486869793170906191158593)
        ·
          refine ⟨27365152344878179643368945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36486869793170906191158593 27365152344878179643368945)
          ·
            refine ⟨20523864258658634732526709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27365152344878179643368945 20523864258658634732526709)
            ·
              refine ⟨1924112274249247006174379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20523864258658634732526709 1924112274249247006174379)
              ·
                refine ⟨2886168411373870509261569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924112274249247006174379 2886168411373870509261569)
                ·
                  refine ⟨2164626308530402881946177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886168411373870509261569 2164626308530402881946177)
                  ·
                    refine ⟨1623469731397802161459633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164626308530402881946177 1623469731397802161459633)
                    ·
                      refine ⟨1217602298548351621094725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623469731397802161459633 1217602298548351621094725)
                      ·
                        rfl

theorem cell23_2371272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_2371272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371272 prefixEnd_2371272 := by exact prefixLift 2371272
  have htrace : WordTrace (prefixWord ++ tailWord_2371272) baseStart_2371272 baseEnd_2371272 := by
    simpa [prefixWord, tailWord_2371272, baseEnd_2371272] using wordTrace_append hprefix tailTrace_2371272
  have hstable : (prefixWord ++ tailWord_2371272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371272).length < 2 ^ (prefixWord ++ tailWord_2371272).sum := by decide
  have hdescent : baseEnd_2371272 < baseStart_2371272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371301 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2371301 : Nat := 118140960795 + 2371301 * 2 ^ 59
def prefixEnd_2371301 : Nat := 4983230072969 + 3 ^ 40 * 2371301 * 2
def baseEnd_2371301 : Nat := 1217617189487332007632091

theorem tailTrace_2371301 : CollatzResearch.WordTrace tailWord_2371301 prefixEnd_2371301 1217617189487332007632091 := by
  unfold tailWord_2371301
  simp only [CollatzResearch.WordTrace]
  refine ⟨86488452782188937813329757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57658968521459291875553171 86488452782188937813329757)
  ·
    refine ⟨32433169793320851679998659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86488452782188937813329757 32433169793320851679998659)
    ·
      refine ⟨48649754689981277519997989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32433169793320851679998659 48649754689981277519997989)
      ·
        refine ⟨9121829004371489534999623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48649754689981277519997989 9121829004371489534999623)
        ·
          refine ⟨13682743506557234302499435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121829004371489534999623 13682743506557234302499435)
          ·
            refine ⟨20524115259835851453749153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13682743506557234302499435 20524115259835851453749153)
            ·
              refine ⟨15393086444876888590311865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20524115259835851453749153 15393086444876888590311865)
              ·
                refine ⟨11544814833657666442733899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15393086444876888590311865 11544814833657666442733899)
                ·
                  refine ⟨17317222250486499664100849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544814833657666442733899 17317222250486499664100849)
                  ·
                    refine ⟨12987916687864874748075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17317222250486499664100849 12987916687864874748075637)
                    ·
                      refine ⟨1217617189487332007632091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12987916687864874748075637 1217617189487332007632091)
                      ·
                        rfl

theorem cell23_2371301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2371301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371301 prefixEnd_2371301 := by exact prefixLift 2371301
  have htrace : WordTrace (prefixWord ++ tailWord_2371301) baseStart_2371301 baseEnd_2371301 := by
    simpa [prefixWord, tailWord_2371301, baseEnd_2371301] using wordTrace_append hprefix tailTrace_2371301
  have hstable : (prefixWord ++ tailWord_2371301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371301).length < 2 ^ (prefixWord ++ tailWord_2371301).sum := by decide
  have hdescent : baseEnd_2371301 < baseStart_2371301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371318 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2371318 : Nat := 118140960795 + 2371318 * 2 ^ 59
def prefixEnd_2371318 : Nat := 4983230072969 + 3 ^ 40 * 2371318 * 2
def baseEnd_2371318 : Nat := 1217625918658458441119513

theorem tailTrace_2371318 : CollatzResearch.WordTrace tailWord_2371318 prefixEnd_2371318 1217625918658458441119513 := by
  unfold tailWord_2371318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405567051445459357293663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57659381882084899811132405 5405567051445459357293663)
  ·
    refine ⟨8108350577168189035940495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405567051445459357293663 8108350577168189035940495)
    ·
      refine ⟨12162525865752283553910743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8108350577168189035940495 12162525865752283553910743)
      ·
        refine ⟨18243788798628425330866115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162525865752283553910743 18243788798628425330866115)
        ·
          refine ⟨27365683197942637996299173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243788798628425330866115 27365683197942637996299173)
          ·
            refine ⟨5131065599614244624306095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27365683197942637996299173 5131065599614244624306095)
            ·
              refine ⟨7696598399421366936459143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131065599614244624306095 7696598399421366936459143)
              ·
                refine ⟨11544897599132050404688715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696598399421366936459143 11544897599132050404688715)
                ·
                  refine ⟨17317346398698075607033073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544897599132050404688715 17317346398698075607033073)
                  ·
                    refine ⟨12988009799023556705274805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17317346398698075607033073 12988009799023556705274805)
                    ·
                      refine ⟨1217625918658458441119513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12988009799023556705274805 1217625918658458441119513)
                      ·
                        rfl

theorem cell23_2371318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2371318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371318 prefixEnd_2371318 := by exact prefixLift 2371318
  have htrace : WordTrace (prefixWord ++ tailWord_2371318) baseStart_2371318 baseEnd_2371318 := by
    simpa [prefixWord, tailWord_2371318, baseEnd_2371318] using wordTrace_append hprefix tailTrace_2371318
  have hstable : (prefixWord ++ tailWord_2371318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371318).length < 2 ^ (prefixWord ++ tailWord_2371318).sum := by decide
  have hdescent : baseEnd_2371318 < baseStart_2371318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371331 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3]
def baseStart_2371331 : Nat := 118140960795 + 2371331 * 2 ^ 59
def prefixEnd_2371331 : Nat := 4983230072969 + 3 ^ 40 * 2371331 * 2
def baseEnd_2371331 : Nat := 1217632593906966890256953

theorem tailTrace_2371331 : CollatzResearch.WordTrace tailWord_2371331 prefixEnd_2371331 1217632593906966890256953 := by
  unfold tailWord_2371331
  simp only [CollatzResearch.WordTrace]
  refine ⟨86489546972080252936921847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57659697981386835291281231 86489546972080252936921847)
  ·
    refine ⟨129734320458120379405382771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86489546972080252936921847 129734320458120379405382771)
    ·
      refine ⟨194601480687180569108074157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129734320458120379405382771 194601480687180569108074157)
      ·
        refine ⟨72975555257692713415527809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194601480687180569108074157 72975555257692713415527809)
        ·
          refine ⟨54731666443269535061645857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72975555257692713415527809 54731666443269535061645857)
          ·
            refine ⟨41048749832452151296234393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54731666443269535061645857 41048749832452151296234393)
            ·
              refine ⟨30786562374339113472175795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41048749832452151296234393 30786562374339113472175795)
              ·
                refine ⟨46179843561508670208263693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30786562374339113472175795 46179843561508670208263693)
                ·
                  refine ⟨17317441335565751328098885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46179843561508670208263693 17317441335565751328098885)
                  ·
                    refine ⟨3247020250418578374018541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17317441335565751328098885 3247020250418578374018541)
                    ·
                      refine ⟨1217632593906966890256953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247020250418578374018541 1217632593906966890256953)
                      ·
                        rfl

theorem cell23_2371331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_2371331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371331 prefixEnd_2371331 := by exact prefixLift 2371331
  have htrace : WordTrace (prefixWord ++ tailWord_2371331) baseStart_2371331 baseEnd_2371331 := by
    simpa [prefixWord, tailWord_2371331, baseEnd_2371331] using wordTrace_append hprefix tailTrace_2371331
  have hstable : (prefixWord ++ tailWord_2371331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371331).length < 2 ^ (prefixWord ++ tailWord_2371331).sum := by decide
  have hdescent : baseEnd_2371331 < baseStart_2371331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371368 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 6]
def baseStart_2371368 : Nat := 118140960795 + 2371368 * 2 ^ 59
def prefixEnd_2371368 : Nat := 4983230072969 + 3 ^ 40 * 2371368 * 2
def baseEnd_2371368 : Nat := 135294621410131471721587

theorem tailTrace_2371368 : CollatzResearch.WordTrace tailWord_2371368 prefixEnd_2371368 135294621410131471721587 := by
  unfold tailWord_2371368
  simp only [CollatzResearch.WordTrace]
  refine ⟨43245448236473104128009379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57660597648630805504012505 43245448236473104128009379)
  ·
    refine ⟨64868172354709656192014069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43245448236473104128009379 64868172354709656192014069)
    ·
      refine ⟨6081391158254030268001319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64868172354709656192014069 6081391158254030268001319)
      ·
        refine ⟨9122086737381045402001979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081391158254030268001319 9122086737381045402001979)
        ·
          refine ⟨13683130106071568103002969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122086737381045402001979 13683130106071568103002969)
          ·
            refine ⟨10262347579553676077252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13683130106071568103002969 10262347579553676077252227)
            ·
              refine ⟨15393521369330514115878341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262347579553676077252227 15393521369330514115878341)
              ·
                refine ⟨2886285256749471396727189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15393521369330514115878341 2886285256749471396727189)
                ·
                  refine ⟨135294621410131471721587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2886285256749471396727189 135294621410131471721587)
                  ·
                    rfl

theorem cell23_2371368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_2371368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371368 prefixEnd_2371368 := by exact prefixLift 2371368
  have htrace : WordTrace (prefixWord ++ tailWord_2371368) baseStart_2371368 baseEnd_2371368 := by
    simpa [prefixWord, tailWord_2371368, baseEnd_2371368] using wordTrace_append hprefix tailTrace_2371368
  have hstable : (prefixWord ++ tailWord_2371368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371368).length < 2 ^ (prefixWord ++ tailWord_2371368).sum := by decide
  have hdescent : baseEnd_2371368 < baseStart_2371368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371372 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_2371372 : Nat := 118140960795 + 2371372 * 2 ^ 59
def prefixEnd_2371372 : Nat := 4983230072969 + 3 ^ 40 * 2371372 * 2
def baseEnd_2371372 : Nat := 405884548871267076614755

theorem tailTrace_2371372 : CollatzResearch.WordTrace tailWord_2371372 prefixEnd_2371372 405884548871267076614755 := by
  unfold tailWord_2371372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43245521182465858469582185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57660694909954477959442913 43245521182465858469582185)
  ·
    refine ⟨32434140886849393852186639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43245521182465858469582185 32434140886849393852186639)
    ·
      refine ⟨48651211330274090778279959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32434140886849393852186639 48651211330274090778279959)
      ·
        refine ⟨72976816995411136167419939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48651211330274090778279959 72976816995411136167419939)
        ·
          refine ⟨109465225493116704251129909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72976816995411136167419939 109465225493116704251129909)
          ·
            refine ⟨10262364889979691023543429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109465225493116704251129909 10262364889979691023543429)
            ·
              refine ⟨1924193416871192066914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10262364889979691023543429 1924193416871192066914393)
              ·
                refine ⟨1443145062653394050185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924193416871192066914393 1443145062653394050185795)
                ·
                  refine ⟨2164717593980091075278693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443145062653394050185795 2164717593980091075278693)
                  ·
                    refine ⟨405884548871267076614755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164717593980091075278693 405884548871267076614755)
                    ·
                      rfl

theorem cell23_2371372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_2371372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371372 prefixEnd_2371372 := by exact prefixLift 2371372
  have htrace : WordTrace (prefixWord ++ tailWord_2371372) baseStart_2371372 baseEnd_2371372 := by
    simpa [prefixWord, tailWord_2371372, baseEnd_2371372] using wordTrace_append hprefix tailTrace_2371372
  have hstable : (prefixWord ++ tailWord_2371372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371372).length < 2 ^ (prefixWord ++ tailWord_2371372).sum := by decide
  have hdescent : baseEnd_2371372 < baseStart_2371372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371395 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 3]
def baseStart_2371395 : Nat := 118140960795 + 2371395 * 2 ^ 59
def prefixEnd_2371395 : Nat := 4983230072969 + 3 ^ 40 * 2371395 * 2
def baseEnd_2371395 : Nat := 1217665456668854639856659

theorem tailTrace_2371395 : CollatzResearch.WordTrace tailWord_2371395 prefixEnd_2371395 1217665456668854639856659 := by
  unfold tailWord_2371395
  simp only [CollatzResearch.WordTrace]
  refine ⟨86491881243848391867251639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57661254162565594578167759 86491881243848391867251639)
  ·
    refine ⟨129737821865772587800877459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86491881243848391867251639 129737821865772587800877459)
    ·
      refine ⟨194606732798658881701316189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129737821865772587800877459 194606732798658881701316189)
      ·
        refine ⟨72977524799497080637993571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194606732798658881701316189 72977524799497080637993571)
        ·
          refine ⟨109466287199245620956990357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72977524799497080637993571 109466287199245620956990357)
          ·
            refine ⟨5131232212464638482358923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109466287199245620956990357 5131232212464638482358923)
            ·
              refine ⟨7696848318696957723538385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131232212464638482358923 7696848318696957723538385)
              ·
                refine ⟨5772636239022718292653789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7696848318696957723538385 5772636239022718292653789)
                ·
                  refine ⟨2164738589633519359745171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5772636239022718292653789 2164738589633519359745171)
                  ·
                    refine ⟨3247107884450279039617757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164738589633519359745171 3247107884450279039617757)
                    ·
                      refine ⟨1217665456668854639856659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247107884450279039617757 1217665456668854639856659)
                      ·
                        rfl

theorem cell23_2371395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_2371395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371395 prefixEnd_2371395 := by exact prefixLift 2371395
  have htrace : WordTrace (prefixWord ++ tailWord_2371395) baseStart_2371395 baseEnd_2371395 := by
    simpa [prefixWord, tailWord_2371395, baseEnd_2371395] using wordTrace_append hprefix tailTrace_2371395
  have hstable : (prefixWord ++ tailWord_2371395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371395).length < 2 ^ (prefixWord ++ tailWord_2371395).sum := by decide
  have hdescent : baseEnd_2371395 < baseStart_2371395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371415 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 1, 5]
def baseStart_2371415 : Nat := 118140960795 + 2371415 * 2 ^ 59
def prefixEnd_2371415 : Nat := 4983230072969 + 3 ^ 40 * 2371415 * 2
def baseEnd_2371415 : Nat := 405891908760648187202189

theorem tailTrace_2371415 : CollatzResearch.WordTrace tailWord_2371415 prefixEnd_2371415 405891908760648187202189 := by
  unfold tailWord_2371415
  simp only [CollatzResearch.WordTrace]
  refine ⟨86492610703775935282979699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57661740469183956855319799 86492610703775935282979699)
  ·
    refine ⟨129738916055663902924469549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86492610703775935282979699 129738916055663902924469549)
    ·
      refine ⟨48652093520873963596676081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129738916055663902924469549 48652093520873963596676081)
      ·
        refine ⟨36489070140655472697507061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48652093520873963596676081 36489070140655472697507061)
        ·
          refine ⟨3420850325686450565391287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36489070140655472697507061 3420850325686450565391287)
          ·
            refine ⟨5131275488529675848086931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420850325686450565391287 5131275488529675848086931)
            ·
              refine ⟨7696913232794513772130397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131275488529675848086931 7696913232794513772130397)
              ·
                refine ⟨2886342462297942664548899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7696913232794513772130397 2886342462297942664548899)
                ·
                  refine ⟨4329513693446913996823349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886342462297942664548899 4329513693446913996823349)
                  ·
                    refine ⟨405891908760648187202189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4329513693446913996823349 405891908760648187202189)
                    ·
                      rfl

theorem cell23_2371415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_2371415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371415 prefixEnd_2371415 := by exact prefixLift 2371415
  have htrace : WordTrace (prefixWord ++ tailWord_2371415) baseStart_2371415 baseEnd_2371415 := by
    simpa [prefixWord, tailWord_2371415, baseEnd_2371415] using wordTrace_append hprefix tailTrace_2371415
  have hstable : (prefixWord ++ tailWord_2371415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371415).length < 2 ^ (prefixWord ++ tailWord_2371415).sum := by decide
  have hdescent : baseEnd_2371415 < baseStart_2371415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371441 : List Nat := [1, 2, 2, 2, 1, 3, 2, 10]
def baseStart_2371441 : Nat := 118140960795 + 2371441 * 2 ^ 59
def prefixEnd_2371441 : Nat := 4983230072969 + 3 ^ 40 * 2371441 * 2
def baseEnd_2371441 : Nat := 45099595436257831847461

theorem tailTrace_2371441 : CollatzResearch.WordTrace tailWord_2371441 prefixEnd_2371441 45099595436257831847461 := by
  unfold tailWord_2371441
  simp only [CollatzResearch.WordTrace]
  refine ⟨86493559001681741723426177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57662372667787827815617451 86493559001681741723426177)
  ·
    refine ⟨64870169251261306292569633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86493559001681741723426177 64870169251261306292569633)
    ·
      refine ⟨48652626938445979719427225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64870169251261306292569633 48652626938445979719427225)
      ·
        refine ⟨36489470203834484789570419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48652626938445979719427225 36489470203834484789570419)
        ·
          refine ⟨54734205305751727184355629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36489470203834484789570419 54734205305751727184355629)
          ·
            refine ⟨20525326989656897694133361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54734205305751727184355629 20525326989656897694133361)
            ·
              refine ⟨15393995242242673270600021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20525326989656897694133361 15393995242242673270600021)
              ·
                refine ⟨45099595436257831847461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15393995242242673270600021 45099595436257831847461)
                ·
                  rfl

theorem cell23_2371441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 10].length) (baseStart_2371441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371441 prefixEnd_2371441 := by exact prefixLift 2371441
  have htrace : WordTrace (prefixWord ++ tailWord_2371441) baseStart_2371441 baseEnd_2371441 := by
    simpa [prefixWord, tailWord_2371441, baseEnd_2371441] using wordTrace_append hprefix tailTrace_2371441
  have hstable : (prefixWord ++ tailWord_2371441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371441).length < 2 ^ (prefixWord ++ tailWord_2371441).sum := by decide
  have hdescent : baseEnd_2371441 < baseStart_2371441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371468 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2371468 : Nat := 118140960795 + 2371468 * 2 ^ 59
def prefixEnd_2371468 : Nat := 4983230072969 + 3 ^ 40 * 2371468 * 2
def baseEnd_2371468 : Nat := 1217702940756632854243823

theorem tailTrace_2371468 : CollatzResearch.WordTrace tailWord_2371468 prefixEnd_2371468 1217702940756632854243823 := by
  unfold tailWord_2371468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43247271886291962667329529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57663029181722616889772705 43247271886291962667329529)
  ·
    refine ⟨32435453914718972000497147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43247271886291962667329529 32435453914718972000497147)
    ·
      refine ⟨48653180872078458000745721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32435453914718972000497147 48653180872078458000745721)
      ·
        refine ⟨36489885654058843500559291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48653180872078458000745721 36489885654058843500559291)
        ·
          refine ⟨54734828481088265250838937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36489885654058843500559291 54734828481088265250838937)
          ·
            refine ⟨41051121360816198938129203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54734828481088265250838937 41051121360816198938129203)
            ·
              refine ⟨61576682041224298407193805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41051121360816198938129203 61576682041224298407193805)
              ·
                refine ⟨23091255765459111902697677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61576682041224298407193805 23091255765459111902697677)
                ·
                  refine ⟨8659220912047166963511629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23091255765459111902697677 8659220912047166963511629)
                  ·
                    refine ⟨3247207842017687611316861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8659220912047166963511629 3247207842017687611316861)
                    ·
                      refine ⟨1217702940756632854243823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247207842017687611316861 1217702940756632854243823)
                      ·
                        rfl

theorem cell23_2371468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2371468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371468 prefixEnd_2371468 := by exact prefixLift 2371468
  have htrace : WordTrace (prefixWord ++ tailWord_2371468) baseStart_2371468 baseEnd_2371468 := by
    simpa [prefixWord, tailWord_2371468, baseEnd_2371468] using wordTrace_append hprefix tailTrace_2371468
  have hstable : (prefixWord ++ tailWord_2371468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371468).length < 2 ^ (prefixWord ++ tailWord_2371468).sum := by decide
  have hdescent : baseEnd_2371468 < baseStart_2371468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371555 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2371555 : Nat := 118140960795 + 2371555 * 2 ^ 59
def prefixEnd_2371555 : Nat := 4983230072969 + 3 ^ 40 * 2371555 * 2
def baseEnd_2371555 : Nat := 1217747613573574013855923

theorem tailTrace_2371555 : CollatzResearch.WordTrace tailWord_2371555 prefixEnd_2371555 1217747613573574013855923 := by
  unfold tailWord_2371555
  simp only [CollatzResearch.WordTrace]
  refine ⟨86497716923268739193076119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57665144615512492795384079 86497716923268739193076119)
  ·
    refine ⟨129746575384903108789614179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86497716923268739193076119 129746575384903108789614179)
    ·
      refine ⟨194619863077354663184421269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129746575384903108789614179 194619863077354663184421269)
      ·
        refine ⟨9122806081750999836769747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194619863077354663184421269 9122806081750999836769747)
        ·
          refine ⟨13684209122626499755154621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122806081750999836769747 13684209122626499755154621)
          ·
            refine ⟨5131578420984937408182983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13684209122626499755154621 5131578420984937408182983)
            ·
              refine ⟨7697367631477406112274475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131578420984937408182983 7697367631477406112274475)
              ·
                refine ⟨11546051447216109168411713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7697367631477406112274475 11546051447216109168411713)
                ·
                  refine ⟨8659538585412081876308785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11546051447216109168411713 8659538585412081876308785)
                  ·
                    refine ⟨6494653939059061407231589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8659538585412081876308785 6494653939059061407231589)
                    ·
                      refine ⟨1217747613573574013855923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6494653939059061407231589 1217747613573574013855923)
                      ·
                        rfl

theorem cell23_2371555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2371555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371555 prefixEnd_2371555 := by exact prefixLift 2371555
  have htrace : WordTrace (prefixWord ++ tailWord_2371555) baseStart_2371555 baseEnd_2371555 := by
    simpa [prefixWord, tailWord_2371555, baseEnd_2371555] using wordTrace_append hprefix tailTrace_2371555
  have hstable : (prefixWord ++ tailWord_2371555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371555).length < 2 ^ (prefixWord ++ tailWord_2371555).sum := by decide
  have hdescent : baseEnd_2371555 < baseStart_2371555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371559 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2371559 : Nat := 118140960795 + 2371559 * 2 ^ 59
def prefixEnd_2371559 : Nat := 4983230072969 + 3 ^ 40 * 2371559 * 2
def baseEnd_2371559 : Nat := 1217749667496191998205905

theorem tailTrace_2371559 : CollatzResearch.WordTrace tailWord_2371559 prefixEnd_2371559 1217749667496191998205905 := by
  unfold tailWord_2371559
  simp only [CollatzResearch.WordTrace]
  refine ⟨86497862815254247876221731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57665241876836165250814487 86497862815254247876221731)
  ·
    refine ⟨129746794222881371814332597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86497862815254247876221731 129746794222881371814332597)
    ·
      refine ⟨12163761958395128607593681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129746794222881371814332597 12163761958395128607593681)
      ·
        refine ⟨9122821468796346455695261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163761958395128607593681 9122821468796346455695261)
        ·
          refine ⟨3421058050798629920885723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9122821468796346455695261 3421058050798629920885723)
          ·
            refine ⟨5131587076197944881328585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421058050798629920885723 5131587076197944881328585)
            ·
              refine ⟨3848690307148458660996439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5131587076197944881328585 3848690307148458660996439)
              ·
                refine ⟨5773035460722687991494659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848690307148458660996439 5773035460722687991494659)
                ·
                  refine ⟨8659553191084031987241989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773035460722687991494659 8659553191084031987241989)
                  ·
                    refine ⟨1623666223328255997607873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8659553191084031987241989 1623666223328255997607873)
                    ·
                      refine ⟨1217749667496191998205905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623666223328255997607873 1217749667496191998205905)
                      ·
                        rfl

theorem cell23_2371559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2371559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371559 prefixEnd_2371559 := by exact prefixLift 2371559
  have htrace : WordTrace (prefixWord ++ tailWord_2371559) baseStart_2371559 baseEnd_2371559 := by
    simpa [prefixWord, tailWord_2371559, baseEnd_2371559] using wordTrace_append hprefix tailTrace_2371559
  have hstable : (prefixWord ++ tailWord_2371559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371559).length < 2 ^ (prefixWord ++ tailWord_2371559).sum := by decide
  have hdescent : baseEnd_2371559 < baseStart_2371559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371628 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2371628 : Nat := 118140960795 + 2371628 * 2 ^ 59
def prefixEnd_2371628 : Nat := 4983230072969 + 3 ^ 40 * 2371628 * 2
def baseEnd_2371628 : Nat := 1217785097661352228243087

theorem tailTrace_2371628 : CollatzResearch.WordTrace tailWord_2371628 prefixEnd_2371628 1217785097661352228243087 := by
  unfold tailWord_2371628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43250189726002136330241769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57666919634669515106989025 43250189726002136330241769)
  ·
    refine ⟨32437642294501602247681327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43250189726002136330241769 32437642294501602247681327)
    ·
      refine ⟨48656463441752403371521991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32437642294501602247681327 48656463441752403371521991)
      ·
        refine ⟨72984695162628605057282987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48656463441752403371521991 72984695162628605057282987)
        ·
          refine ⟨109477042743942907585924481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72984695162628605057282987 109477042743942907585924481)
          ·
            refine ⟨82107782057957180689443361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109477042743942907585924481 82107782057957180689443361)
            ·
              refine ⟨61580836543467885517082521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82107782057957180689443361 61580836543467885517082521)
              ·
                refine ⟨46185627407600914137811891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61580836543467885517082521 46185627407600914137811891)
                ·
                  refine ⟨69278441111401371206717837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46185627407600914137811891 69278441111401371206717837)
                  ·
                    refine ⟨25979415416775514202519189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69278441111401371206717837 25979415416775514202519189)
                    ·
                      refine ⟨1217785097661352228243087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25979415416775514202519189 1217785097661352228243087)
                      ·
                        rfl

theorem cell23_2371628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2371628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371628 prefixEnd_2371628 := by exact prefixLift 2371628
  have htrace : WordTrace (prefixWord ++ tailWord_2371628) baseStart_2371628 baseEnd_2371628 := by
    simpa [prefixWord, tailWord_2371628, baseEnd_2371628] using wordTrace_append hprefix tailTrace_2371628
  have hstable : (prefixWord ++ tailWord_2371628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371628).length < 2 ^ (prefixWord ++ tailWord_2371628).sum := by decide
  have hdescent : baseEnd_2371628 < baseStart_2371628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371635 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3]
def baseStart_2371635 : Nat := 118140960795 + 2371635 * 2 ^ 59
def prefixEnd_2371635 : Nat := 4983230072969 + 3 ^ 40 * 2371635 * 2
def baseEnd_2371635 : Nat := 1217788692025933700855555

theorem tailTrace_2371635 : CollatzResearch.WordTrace tailWord_2371635 prefixEnd_2371635 1217788692025933700855555 := by
  unfold tailWord_2371635
  simp only [CollatzResearch.WordTrace]
  refine ⟨86500634762978912855988359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57667089841985941903992239 86500634762978912855988359)
  ·
    refine ⟨129750952144468369283982539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86500634762978912855988359 129750952144468369283982539)
    ·
      refine ⟨194626428216702553925973809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129750952144468369283982539 194626428216702553925973809)
      ·
        refine ⟨145969821162526915444480357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194626428216702553925973809 145969821162526915444480357)
        ·
          refine ⟨27369341467973796645840067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145969821162526915444480357 27369341467973796645840067)
          ·
            refine ⟨41054012201960694968760101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27369341467973796645840067 41054012201960694968760101)
            ·
              refine ⟨7697627287867630306642519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41054012201960694968760101 7697627287867630306642519)
              ·
                refine ⟨11546440931801445459963779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7697627287867630306642519 11546440931801445459963779)
                ·
                  refine ⟨17319661397702168189945669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11546440931801445459963779 17319661397702168189945669)
                  ·
                    refine ⟨3247436512069156535614813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17319661397702168189945669 3247436512069156535614813)
                    ·
                      refine ⟨1217788692025933700855555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247436512069156535614813 1217788692025933700855555)
                      ·
                        rfl

theorem cell23_2371635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_2371635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371635 prefixEnd_2371635 := by exact prefixLift 2371635
  have htrace : WordTrace (prefixWord ++ tailWord_2371635) baseStart_2371635 baseEnd_2371635 := by
    simpa [prefixWord, tailWord_2371635, baseEnd_2371635] using wordTrace_append hprefix tailTrace_2371635
  have hstable : (prefixWord ++ tailWord_2371635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371635).length < 2 ^ (prefixWord ++ tailWord_2371635).sum := by decide
  have hdescent : baseEnd_2371635 < baseStart_2371635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371655 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 6]
def baseStart_2371655 : Nat := 118140960795 + 2371655 * 2 ^ 59
def prefixEnd_2371655 : Nat := 4983230072969 + 3 ^ 40 * 2371655 * 2
def baseEnd_2371655 : Nat := 135310995737669291400607

theorem tailTrace_2371655 : CollatzResearch.WordTrace tailWord_2371655 prefixEnd_2371655 135310995737669291400607 := by
  unfold tailWord_2371655
  simp only [CollatzResearch.WordTrace]
  refine ⟨86501364222906456271716419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57667576148604304181144279 86501364222906456271716419)
  ·
    refine ⟨129752046334359684407574629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86501364222906456271716419 129752046334359684407574629)
    ·
      refine ⟨24328508687692440826420243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129752046334359684407574629 24328508687692440826420243)
      ·
        refine ⟨36492763031538661239630365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24328508687692440826420243 36492763031538661239630365)
        ·
          refine ⟨13684786136826997964861387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36492763031538661239630365 13684786136826997964861387)
          ·
            refine ⟨20527179205240496947292081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13684786136826997964861387 20527179205240496947292081)
            ·
              refine ⟨15395384403930372710469061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20527179205240496947292081 15395384403930372710469061)
              ·
                refine ⟨2886634575736944883212949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15395384403930372710469061 2886634575736944883212949)
                ·
                  refine ⟨135310995737669291400607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2886634575736944883212949 135310995737669291400607)
                  ·
                    rfl

theorem cell23_2371655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 6].length) (baseStart_2371655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371655 prefixEnd_2371655 := by exact prefixLift 2371655
  have htrace : WordTrace (prefixWord ++ tailWord_2371655) baseStart_2371655 baseEnd_2371655 := by
    simpa [prefixWord, tailWord_2371655, baseEnd_2371655] using wordTrace_append hprefix tailTrace_2371655
  have hstable : (prefixWord ++ tailWord_2371655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371655).length < 2 ^ (prefixWord ++ tailWord_2371655).sum := by decide
  have hdescent : baseEnd_2371655 < baseStart_2371655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371672 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 6]
def baseStart_2371672 : Nat := 118140960795 + 2371672 * 2 ^ 59
def prefixEnd_2371672 : Nat := 4983230072969 + 3 ^ 40 * 2371672 * 2
def baseEnd_2371672 : Nat := 135311965645572228454765

theorem tailTrace_2371672 : CollatzResearch.WordTrace tailWord_2371672 prefixEnd_2371672 135311965645572228454765 := by
  unfold tailWord_2371672
  simp only [CollatzResearch.WordTrace]
  refine ⟨43250992131922434087542635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57667989509229912116723513 43250992131922434087542635)
  ·
    refine ⟨64876488197883651131313953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43250992131922434087542635 64876488197883651131313953)
    ·
      refine ⟨48657366148412738348485465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64876488197883651131313953 48657366148412738348485465)
      ·
        refine ⟨36493024611309553761364099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48657366148412738348485465 36493024611309553761364099)
        ·
          refine ⟨54739536916964330642046149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36493024611309553761364099 54739536916964330642046149)
          ·
            refine ⟨10263663171930811995383653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54739536916964330642046149 10263663171930811995383653)
            ·
              refine ⟨1924436844737027249134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10263663171930811995383653 1924436844737027249134435)
              ·
                refine ⟨2886655267105540873701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924436844737027249134435 2886655267105540873701653)
                ·
                  refine ⟨135311965645572228454765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2886655267105540873701653 135311965645572228454765)
                  ·
                    rfl

theorem cell23_2371672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_2371672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371672 prefixEnd_2371672 := by exact prefixLift 2371672
  have htrace : WordTrace (prefixWord ++ tailWord_2371672) baseStart_2371672 baseEnd_2371672 := by
    simpa [prefixWord, tailWord_2371672, baseEnd_2371672] using wordTrace_append hprefix tailTrace_2371672
  have hstable : (prefixWord ++ tailWord_2371672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371672).length < 2 ^ (prefixWord ++ tailWord_2371672).sum := by decide
  have hdescent : baseEnd_2371672 < baseStart_2371672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371709 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_2371709 : Nat := 118140960795 + 2371709 * 2 ^ 59
def prefixEnd_2371709 : Nat := 4983230072969 + 3 ^ 40 * 2371709 * 2
def baseEnd_2371709 : Nat := 1217826689594366411330215

theorem tailTrace_2371709 : CollatzResearch.WordTrace tailWord_2371709 prefixEnd_2371709 1217826689594366411330215 := by
  unfold tailWord_2371709
  simp only [CollatzResearch.WordTrace]
  refine ⟨86503333764710823494182181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57668889176473882329454787 86503333764710823494182181)
  ·
    refine ⟨16219375080883279405159159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86503333764710823494182181 16219375080883279405159159)
    ·
      refine ⟨24329062621324919107738739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219375080883279405159159 24329062621324919107738739)
      ·
        refine ⟨36493593931987378661608109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24329062621324919107738739 36493593931987378661608109)
        ·
          refine ⟨13685097724495266998103041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36493593931987378661608109 13685097724495266998103041)
          ·
            refine ⟨10263823293371450248577281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13685097724495266998103041 10263823293371450248577281)
            ·
              refine ⟨7697867470028587686432961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10263823293371450248577281 7697867470028587686432961)
              ·
                refine ⟨5773400602521440764824721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7697867470028587686432961 5773400602521440764824721)
                ·
                  refine ⟨4330050451891080573618541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773400602521440764824721 4330050451891080573618541)
                  ·
                    refine ⟨1623768919459155215106953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4330050451891080573618541 1623768919459155215106953)
                    ·
                      refine ⟨1217826689594366411330215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623768919459155215106953 1217826689594366411330215)
                      ·
                        rfl

theorem cell23_2371709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_2371709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371709 prefixEnd_2371709 := by exact prefixLift 2371709
  have htrace : WordTrace (prefixWord ++ tailWord_2371709) baseStart_2371709 baseEnd_2371709 := by
    simpa [prefixWord, tailWord_2371709, baseEnd_2371709] using wordTrace_append hprefix tailTrace_2371709
  have hstable : (prefixWord ++ tailWord_2371709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371709).length < 2 ^ (prefixWord ++ tailWord_2371709).sum := by decide
  have hdescent : baseEnd_2371709 < baseStart_2371709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371716 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_2371716 : Nat := 118140960795 + 2371716 * 2 ^ 59
def prefixEnd_2371716 : Nat := 4983230072969 + 3 ^ 40 * 2371716 * 2
def baseEnd_2371716 : Nat := 1217830283958947883942683

theorem tailTrace_2371716 : CollatzResearch.WordTrace tailWord_2371716 prefixEnd_2371716 1217830283958947883942683 := by
  unfold tailWord_2371716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43251794537842731844843501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57669059383790309126458001 43251794537842731844843501)
  ·
    refine ⟨16219422951691024441816313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43251794537842731844843501 16219422951691024441816313)
    ·
      refine ⟨12164567213768268331362235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16219422951691024441816313 12164567213768268331362235)
      ·
        refine ⟨18246850820652402497043353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12164567213768268331362235 18246850820652402497043353)
        ·
          refine ⟨13685138115489301872782515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18246850820652402497043353 13685138115489301872782515)
          ·
            refine ⟨20527707173233952809173773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685138115489301872782515 20527707173233952809173773)
            ·
              refine ⟨7697890189962732303440165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20527707173233952809173773 7697890189962732303440165)
              ·
                refine ⟨1443354410618012306895031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7697890189962732303440165 1443354410618012306895031)
                ·
                  refine ⟨2165031615927018460342547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443354410618012306895031 2165031615927018460342547)
                  ·
                    refine ⟨3247547423890527690513821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165031615927018460342547 3247547423890527690513821)
                    ·
                      refine ⟨1217830283958947883942683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247547423890527690513821 1217830283958947883942683)
                      ·
                        rfl

theorem cell23_2371716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_2371716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371716 prefixEnd_2371716 := by exact prefixLift 2371716
  have htrace : WordTrace (prefixWord ++ tailWord_2371716) baseStart_2371716 baseEnd_2371716 := by
    simpa [prefixWord, tailWord_2371716, baseEnd_2371716] using wordTrace_append hprefix tailTrace_2371716
  have hstable : (prefixWord ++ tailWord_2371716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371716).length < 2 ^ (prefixWord ++ tailWord_2371716).sum := by decide
  have hdescent : baseEnd_2371716 < baseStart_2371716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371722 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2371722 : Nat := 118140960795 + 2371722 * 2 ^ 59
def prefixEnd_2371722 : Nat := 4983230072969 + 3 ^ 40 * 2371722 * 2
def baseEnd_2371722 : Nat := 1217833364842874860467655

theorem tailTrace_2371722 : CollatzResearch.WordTrace tailWord_2371722 prefixEnd_2371722 1217833364842874860467655 := by
  unfold tailWord_2371722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21625951978415931678601355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57669205275775817809603613 21625951978415931678601355)
  ·
    refine ⟨32438927967623897517902033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21625951978415931678601355 32438927967623897517902033)
    ·
      refine ⟨24329195975717923138426525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32438927967623897517902033 24329195975717923138426525)
      ·
        refine ⟨9123448490894221176909947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24329195975717923138426525 9123448490894221176909947)
        ·
          refine ⟨13685172736341331765364921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123448490894221176909947 13685172736341331765364921)
          ·
            refine ⟨10263879552255998824023691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13685172736341331765364921 10263879552255998824023691)
            ·
              refine ⟨15395819328383998236035537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263879552255998824023691 15395819328383998236035537)
              ·
                refine ⟨11546864496287998677026653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15395819328383998236035537 11546864496287998677026653)
                ·
                  refine ⟨4330074186107999503884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11546864496287998677026653 4330074186107999503884995)
                  ·
                    refine ⟨6495111279161999255827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330074186107999503884995 6495111279161999255827493)
                    ·
                      refine ⟨1217833364842874860467655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6495111279161999255827493 1217833364842874860467655)
                      ·
                        rfl

theorem cell23_2371722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2371722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371722 prefixEnd_2371722 := by exact prefixLift 2371722
  have htrace : WordTrace (prefixWord ++ tailWord_2371722) baseStart_2371722 baseEnd_2371722 := by
    simpa [prefixWord, tailWord_2371722, baseEnd_2371722] using wordTrace_append hprefix tailTrace_2371722
  have hstable : (prefixWord ++ tailWord_2371722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371722).length < 2 ^ (prefixWord ++ tailWord_2371722).sum := by decide
  have hdescent : baseEnd_2371722 < baseStart_2371722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3]
def baseStart_2371755 : Nat := 118140960795 + 2371755 * 2 ^ 59
def prefixEnd_2371755 : Nat := 4983230072969 + 3 ^ 40 * 2371755 * 2
def baseEnd_2371755 : Nat := 1217850309704473231355003

theorem tailTrace_2371755 : CollatzResearch.WordTrace tailWord_2371755 prefixEnd_2371755 1217850309704473231355003 := by
  unfold tailWord_2371755
  simp only [CollatzResearch.WordTrace]
  refine ⟨86505011522544173350356719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57670007681696115566904479 86505011522544173350356719)
  ·
    refine ⟨129757517283816260025535079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86505011522544173350356719 129757517283816260025535079)
    ·
      refine ⟨194636275925724390038302619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129757517283816260025535079 194636275925724390038302619)
      ·
        refine ⟨291954413888586585057453929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194636275925724390038302619 291954413888586585057453929)
        ·
          refine ⟨218965810416439938793090447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291954413888586585057453929 218965810416439938793090447)
          ·
            refine ⟨328448715624659908189635671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218965810416439938793090447 328448715624659908189635671)
            ·
              refine ⟨492673073436989862284453507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328448715624659908189635671 492673073436989862284453507)
              ·
                refine ⟨739009610155484793426680261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492673073436989862284453507 739009610155484793426680261)
                ·
                  refine ⟨138564301904153398767502549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739009610155484793426680261 138564301904153398767502549)
                  ·
                    refine ⟨3247600825878595283613341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138564301904153398767502549 3247600825878595283613341)
                    ·
                      refine ⟨1217850309704473231355003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247600825878595283613341 1217850309704473231355003)
                      ·
                        rfl

theorem cell23_2371755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].length) (baseStart_2371755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371755 prefixEnd_2371755 := by exact prefixLift 2371755
  have htrace : WordTrace (prefixWord ++ tailWord_2371755) baseStart_2371755 baseEnd_2371755 := by
    simpa [prefixWord, tailWord_2371755, baseEnd_2371755] using wordTrace_append hprefix tailTrace_2371755
  have hstable : (prefixWord ++ tailWord_2371755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371755).length < 2 ^ (prefixWord ++ tailWord_2371755).sum := by decide
  have hdescent : baseEnd_2371755 < baseStart_2371755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371816 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2371816 : Nat := 118140960795 + 2371816 * 2 ^ 59
def prefixEnd_2371816 : Nat := 4983230072969 + 3 ^ 40 * 2371816 * 2
def baseEnd_2371816 : Nat := 1217881632024397492692223

theorem tailTrace_2371816 : CollatzResearch.WordTrace tailWord_2371816 prefixEnd_2371816 1217881632024397492692223 := by
  unfold tailWord_2371816
  simp only [CollatzResearch.WordTrace]
  refine ⟨43253618187661590384163651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57671490916882120512218201 43253618187661590384163651)
  ·
    refine ⟨64880427281492385576245477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43253618187661590384163651 64880427281492385576245477)
    ·
      refine ⟨12165080115279822295546027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64880427281492385576245477 12165080115279822295546027)
      ·
        refine ⟨18247620172919733443319041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12165080115279822295546027 18247620172919733443319041)
        ·
          refine ⟨13685715129689800082489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18247620172919733443319041 13685715129689800082489281)
          ·
            refine ⟨10264286347267350061866961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13685715129689800082489281 10264286347267350061866961)
            ·
              refine ⟨7698214760450512546400221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10264286347267350061866961 7698214760450512546400221)
              ·
                refine ⟨2886830535168942204900083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698214760450512546400221 2886830535168942204900083)
                ·
                  refine ⟨4330245802753413307350125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886830535168942204900083 4330245802753413307350125)
                  ·
                    refine ⟨1623842176032529990256297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4330245802753413307350125 1623842176032529990256297)
                    ·
                      refine ⟨1217881632024397492692223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623842176032529990256297 1217881632024397492692223)
                      ·
                        rfl

theorem cell23_2371816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2371816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371816 prefixEnd_2371816 := by exact prefixLift 2371816
  have htrace : WordTrace (prefixWord ++ tailWord_2371816) baseStart_2371816 baseEnd_2371816 := by
    simpa [prefixWord, tailWord_2371816, baseEnd_2371816] using wordTrace_append hprefix tailTrace_2371816
  have hstable : (prefixWord ++ tailWord_2371816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371816).length < 2 ^ (prefixWord ++ tailWord_2371816).sum := by decide
  have hdescent : baseEnd_2371816 < baseStart_2371816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371855 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_2371855 : Nat := 118140960795 + 2371855 * 2 ^ 59
def prefixEnd_2371855 : Nat := 4983230072969 + 3 ^ 40 * 2371855 * 2
def baseEnd_2371855 : Nat := 1217901657769922840104543

theorem tailTrace_2371855 : CollatzResearch.WordTrace tailWord_2371855 prefixEnd_2371855 1217901657769922840104543 := by
  unfold tailWord_2371855
  simp only [CollatzResearch.WordTrace]
  refine ⟨86508658822181890428997019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57672439214787926952664679 86508658822181890428997019)
  ·
    refine ⟨129762988233272835643495529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86508658822181890428997019 129762988233272835643495529)
    ·
      refine ⟨97322241174954626732621647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129762988233272835643495529 97322241174954626732621647)
      ·
        refine ⟨145983361762431940098932471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97322241174954626732621647 145983361762431940098932471)
        ·
          refine ⟨218975042643647910148398707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145983361762431940098932471 218975042643647910148398707)
          ·
            refine ⟨328462563965471865222598061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218975042643647910148398707 328462563965471865222598061)
            ·
              refine ⟨123173461487051949458474273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328462563965471865222598061 123173461487051949458474273)
              ·
                refine ⟨92380096115288962093855705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123173461487051949458474273 92380096115288962093855705)
                ·
                  refine ⟨69285072086466721570391779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92380096115288962093855705 69285072086466721570391779)
                  ·
                    refine ⟨103927608129700082355587669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69285072086466721570391779 103927608129700082355587669)
                    ·
                      refine ⟨1217901657769922840104543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103927608129700082355587669 1217901657769922840104543)
                      ·
                        rfl

theorem cell23_2371855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_2371855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371855 prefixEnd_2371855 := by exact prefixLift 2371855
  have htrace : WordTrace (prefixWord ++ tailWord_2371855) baseStart_2371855 baseEnd_2371855 := by
    simpa [prefixWord, tailWord_2371855, baseEnd_2371855] using wordTrace_append hprefix tailTrace_2371855
  have hstable : (prefixWord ++ tailWord_2371855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371855).length < 2 ^ (prefixWord ++ tailWord_2371855).sum := by decide
  have hdescent : baseEnd_2371855 < baseStart_2371855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371880 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2371880 : Nat := 118140960795 + 2371880 * 2 ^ 59
def prefixEnd_2371880 : Nat := 4983230072969 + 3 ^ 40 * 2371880 * 2
def baseEnd_2371880 : Nat := 1217914494786285242291929

theorem tailTrace_2371880 : CollatzResearch.WordTrace tailWord_2371880 prefixEnd_2371880 1217914494786285242291929 := by
  unfold tailWord_2371880
  simp only [CollatzResearch.WordTrace]
  refine ⟨43254785323545659849328547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57673047098060879799104729 43254785323545659849328547)
  ·
    refine ⟨64882177985318489773992821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43254785323545659849328547 64882177985318489773992821)
    ·
      refine ⟨6082704186123608416311827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64882177985318489773992821 6082704186123608416311827)
      ·
        refine ⟨9124056279185412624467741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082704186123608416311827 9124056279185412624467741)
        ·
          refine ⟨3421521104694529734175403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9124056279185412624467741 3421521104694529734175403)
          ·
            refine ⟨5132281657041794601263105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421521104694529734175403 5132281657041794601263105)
            ·
              refine ⟨3849211242781345950947329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132281657041794601263105 3849211242781345950947329)
              ·
                refine ⟨2886908432086009463210497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849211242781345950947329 2886908432086009463210497)
                ·
                  refine ⟨2165181324064507097407873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886908432086009463210497 2165181324064507097407873)
                  ·
                    refine ⟨1623885993048380323055905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165181324064507097407873 1623885993048380323055905)
                    ·
                      refine ⟨1217914494786285242291929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623885993048380323055905 1217914494786285242291929)
                      ·
                        rfl

theorem cell23_2371880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2371880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371880 prefixEnd_2371880 := by exact prefixLift 2371880
  have htrace : WordTrace (prefixWord ++ tailWord_2371880) baseStart_2371880 baseEnd_2371880 := by
    simpa [prefixWord, tailWord_2371880, baseEnd_2371880] using wordTrace_append hprefix tailTrace_2371880
  have hstable : (prefixWord ++ tailWord_2371880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371880).length < 2 ^ (prefixWord ++ tailWord_2371880).sum := by decide
  have hdescent : baseEnd_2371880 < baseStart_2371880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371939 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2371939 : Nat := 118140960795 + 2371939 * 2 ^ 59
def prefixEnd_2371939 : Nat := 4983230072969 + 3 ^ 40 * 2371939 * 2
def baseEnd_2371939 : Nat := 1217944790144900511454157

theorem tailTrace_2371939 : CollatzResearch.WordTrace tailWord_2371939 prefixEnd_2371939 1217944790144900511454157 := by
  unfold tailWord_2371939
  simp only [CollatzResearch.WordTrace]
  refine ⟨86511722553877572775054871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57674481702585048516703247 86511722553877572775054871)
  ·
    refine ⟨129767583830816359162582307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86511722553877572775054871 129767583830816359162582307)
    ·
      refine ⟨194651375746224538743873461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129767583830816359162582307 194651375746224538743873461)
      ·
        refine ⟨18248566476208550507238137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194651375746224538743873461 18248566476208550507238137)
        ·
          refine ⟨13686424857156412880428603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18248566476208550507238137 13686424857156412880428603)
          ·
            refine ⟨20529637285734619320642905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13686424857156412880428603 20529637285734619320642905)
            ·
              refine ⟨15397227964300964490482179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20529637285734619320642905 15397227964300964490482179)
              ·
                refine ⟨23095841946451446735723269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15397227964300964490482179 23095841946451446735723269)
                ·
                  refine ⟨4330470364959646262948113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23095841946451446735723269 4330470364959646262948113)
                  ·
                    refine ⟨3247852773719734697211085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330470364959646262948113 3247852773719734697211085)
                    ·
                      refine ⟨1217944790144900511454157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247852773719734697211085 1217944790144900511454157)
                      ·
                        rfl

theorem cell23_2371939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2371939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371939 prefixEnd_2371939 := by exact prefixLift 2371939
  have htrace : WordTrace (prefixWord ++ tailWord_2371939) baseStart_2371939 baseEnd_2371939 := by
    simpa [prefixWord, tailWord_2371939, baseEnd_2371939] using wordTrace_append hprefix tailTrace_2371939
  have hstable : (prefixWord ++ tailWord_2371939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371939).length < 2 ^ (prefixWord ++ tailWord_2371939).sum := by decide
  have hdescent : baseEnd_2371939 < baseStart_2371939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371946 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2371946 : Nat := 118140960795 + 2371946 * 2 ^ 59
def prefixEnd_2371946 : Nat := 4983230072969 + 3 ^ 40 * 2371946 * 2
def baseEnd_2371946 : Nat := 405982794836493994688875

theorem tailTrace_2371946 : CollatzResearch.WordTrace tailWord_2371946 prefixEnd_2371946 405982794836493994688875 := by
  unfold tailWord_2371946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21627994466213053242639923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57674651909901475313706461 21627994466213053242639923)
  ·
    refine ⟨32441991699319579863959885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21627994466213053242639923 32441991699319579863959885)
    ·
      refine ⟨12165746887244842448984957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32441991699319579863959885 12165746887244842448984957)
      ·
        refine ⟨4562155082716815918369359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12165746887244842448984957 4562155082716815918369359)
        ·
          refine ⟨6843232624075223877554039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562155082716815918369359 6843232624075223877554039)
          ·
            refine ⟨10264848936112835816331059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843232624075223877554039 10264848936112835816331059)
            ·
              refine ⟨15397273404169253724496589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264848936112835816331059 15397273404169253724496589)
              ·
                refine ⟨5773977526563470146686221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15397273404169253724496589 5773977526563470146686221)
                ·
                  refine ⟨2165241572461301305007333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5773977526563470146686221 2165241572461301305007333)
                  ·
                    refine ⟨405982794836493994688875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165241572461301305007333 405982794836493994688875)
                    ·
                      rfl

theorem cell23_2371946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2371946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371946 prefixEnd_2371946 := by exact prefixLift 2371946
  have htrace : WordTrace (prefixWord ++ tailWord_2371946) baseStart_2371946 baseEnd_2371946 := by
    simpa [prefixWord, tailWord_2371946, baseEnd_2371946] using wordTrace_append hprefix tailTrace_2371946
  have hstable : (prefixWord ++ tailWord_2371946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371946).length < 2 ^ (prefixWord ++ tailWord_2371946).sum := by decide
  have hdescent : baseEnd_2371946 < baseStart_2371946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372003 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2372003 : Nat := 118140960795 + 2372003 * 2 ^ 59
def prefixEnd_2372003 : Nat := 4983230072969 + 3 ^ 40 * 2372003 * 2
def baseEnd_2372003 : Nat := 1217977652906788261053863

theorem tailTrace_2372003 : CollatzResearch.WordTrace tailWord_2372003 prefixEnd_2372003 1217977652906788261053863 := by
  unfold tailWord_2372003
  simp only [CollatzResearch.WordTrace]
  refine ⟨86514056825645711705384663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57676037883763807803589775 86514056825645711705384663)
  ·
    refine ⟨129771085238468567558076995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86514056825645711705384663 129771085238468567558076995)
    ·
      refine ⟨194656627857702851337115493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129771085238468567558076995 194656627857702851337115493)
      ·
        refine ⟨36498117723319284625709155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194656627857702851337115493 36498117723319284625709155)
        ·
          refine ⟨54747176584978926938563733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36498117723319284625709155 54747176584978926938563733)
          ·
            refine ⟨2566273902420887200245175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54747176584978926938563733 2566273902420887200245175)
            ·
              refine ⟨3849410853631330800367763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566273902420887200245175 3849410853631330800367763)
              ·
                refine ⟨5774116280446996200551645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849410853631330800367763 5774116280446996200551645)
                ·
                  refine ⟨2165293605167623575206867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5774116280446996200551645 2165293605167623575206867)
                  ·
                    refine ⟨3247940407751435362810301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165293605167623575206867 3247940407751435362810301)
                    ·
                      refine ⟨1217977652906788261053863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3247940407751435362810301 1217977652906788261053863)
                      ·
                        rfl

theorem cell23_2372003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2372003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372003 prefixEnd_2372003 := by exact prefixLift 2372003
  have htrace : WordTrace (prefixWord ++ tailWord_2372003) baseStart_2372003 baseEnd_2372003 := by
    simpa [prefixWord, tailWord_2372003, baseEnd_2372003] using wordTrace_append hprefix tailTrace_2372003
  have hstable : (prefixWord ++ tailWord_2372003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372003).length < 2 ^ (prefixWord ++ tailWord_2372003).sum := by decide
  have hdescent : baseEnd_2372003 < baseStart_2372003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372010 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_2372010 : Nat := 118140960795 + 2372010 * 2 ^ 59
def prefixEnd_2372010 : Nat := 4983230072969 + 3 ^ 40 * 2372010 * 2
def baseEnd_2372010 : Nat := 135331249696818859296259

theorem tailTrace_2372010 : CollatzResearch.WordTrace tailWord_2372010 prefixEnd_2372010 135331249696818859296259 := by
  unfold tailWord_2372010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21628578034155087975222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57676208091080234600592989 21628578034155087975222371)
  ·
    refine ⟨32442867051232631962833557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21628578034155087975222371 32442867051232631962833557)
    ·
      refine ⟨1520759393026529623257823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32442867051232631962833557 1520759393026529623257823)
      ·
        refine ⟨2281139089539794434886735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520759393026529623257823 2281139089539794434886735)
        ·
          refine ⟨3421708634309691652330103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281139089539794434886735 3421708634309691652330103)
          ·
            refine ⟨5132562951464537478495155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421708634309691652330103 5132562951464537478495155)
            ·
              refine ⟨7698844427196806217742733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132562951464537478495155 7698844427196806217742733)
              ·
                refine ⟨2887066660198802331653525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698844427196806217742733 2887066660198802331653525)
                ·
                  refine ⟨135331249696818859296259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2887066660198802331653525 135331249696818859296259)
                  ·
                    rfl

theorem cell23_2372010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_2372010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372010 prefixEnd_2372010 := by exact prefixLift 2372010
  have htrace : WordTrace (prefixWord ++ tailWord_2372010) baseStart_2372010 baseEnd_2372010 := by
    simpa [prefixWord, tailWord_2372010, baseEnd_2372010] using wordTrace_append hprefix tailTrace_2372010
  have hstable : (prefixWord ++ tailWord_2372010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372010).length < 2 ^ (prefixWord ++ tailWord_2372010).sum := by decide
  have hdescent : baseEnd_2372010 < baseStart_2372010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372039 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2372039 : Nat := 118140960795 + 2372039 * 2 ^ 59
def prefixEnd_2372039 : Nat := 4983230072969 + 3 ^ 40 * 2372039 * 2
def baseEnd_2372039 : Nat := 1217996138210350120203697

theorem tailTrace_2372039 : CollatzResearch.WordTrace tailWord_2372039 prefixEnd_2372039 1217996138210350120203697 := by
  unfold tailWord_2372039
  simp only [CollatzResearch.WordTrace]
  refine ⟨86515369853515289853695171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57676913235676859902463447 86515369853515289853695171)
  ·
    refine ⟨129773054780272934780542757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86515369853515289853695171 129773054780272934780542757)
    ·
      refine ⟨24332447771301175271351767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129773054780272934780542757 24332447771301175271351767)
      ·
        refine ⟨36498671656951762907027651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24332447771301175271351767 36498671656951762907027651)
        ·
          refine ⟨54748007485427644360541477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36498671656951762907027651 54748007485427644360541477)
          ·
            refine ⟨10265251403517683317601527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54748007485427644360541477 10265251403517683317601527)
            ·
              refine ⟨15397877105276524976402291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10265251403517683317601527 15397877105276524976402291)
              ·
                refine ⟨23096815657914787464603437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15397877105276524976402291 23096815657914787464603437)
                ·
                  refine ⟨8661305871718045299226289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23096815657914787464603437 8661305871718045299226289)
                  ·
                    refine ⟨6495979403788533974419717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8661305871718045299226289 6495979403788533974419717)
                    ·
                      refine ⟨1217996138210350120203697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6495979403788533974419717 1217996138210350120203697)
                      ·
                        rfl

theorem cell23_2372039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2372039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372039 prefixEnd_2372039 := by exact prefixLift 2372039
  have htrace : WordTrace (prefixWord ++ tailWord_2372039) baseStart_2372039 baseEnd_2372039 := by
    simpa [prefixWord, tailWord_2372039, baseEnd_2372039] using wordTrace_append hprefix tailTrace_2372039
  have hstable : (prefixWord ++ tailWord_2372039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372039).length < 2 ^ (prefixWord ++ tailWord_2372039).sum := by decide
  have hdescent : baseEnd_2372039 < baseStart_2372039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372053 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2372053 : Nat := 118140960795 + 2372053 * 2 ^ 59
def prefixEnd_2372053 : Nat := 4983230072969 + 3 ^ 40 * 2372053 * 2
def baseEnd_2372053 : Nat := 406001108979837688476211

theorem tailTrace_2372053 : CollatzResearch.WordTrace tailWord_2372053 prefixEnd_2372053 406001108979837688476211 := by
  unfold tailWord_2372053
  simp only [CollatzResearch.WordTrace]
  refine ⟨86515880475464570244704813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57677253650309713496469875 86515880475464570244704813)
  ·
    refine ⟨32443455178299213841764305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86515880475464570244704813 32443455178299213841764305)
    ·
      refine ⟨24332591383724410381323229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32443455178299213841764305 24332591383724410381323229)
      ·
        refine ⟨9124721768896653892996211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24332591383724410381323229 9124721768896653892996211)
        ·
          refine ⟨13687082653344980839494317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9124721768896653892996211 13687082653344980839494317)
          ·
            refine ⟨5132655995004367814810369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13687082653344980839494317 5132655995004367814810369)
            ·
              refine ⟨3849491996253275861107777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132655995004367814810369 3849491996253275861107777)
              ·
                refine ⟨2887118997189956895830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849491996253275861107777 2887118997189956895830833)
                ·
                  refine ⟨2165339247892467671873125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887118997189956895830833 2165339247892467671873125)
                  ·
                    refine ⟨406001108979837688476211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165339247892467671873125 406001108979837688476211)
                    ·
                      rfl

theorem cell23_2372053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2372053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372053 prefixEnd_2372053 := by exact prefixLift 2372053
  have htrace : WordTrace (prefixWord ++ tailWord_2372053) baseStart_2372053 baseEnd_2372053 := by
    simpa [prefixWord, tailWord_2372053, baseEnd_2372053] using wordTrace_append hprefix tailTrace_2372053
  have hstable : (prefixWord ++ tailWord_2372053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372053).length < 2 ^ (prefixWord ++ tailWord_2372053).sum := by decide
  have hdescent : baseEnd_2372053 < baseStart_2372053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372076 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2372076 : Nat := 118140960795 + 2372076 * 2 ^ 59
def prefixEnd_2372076 : Nat := 4983230072969 + 3 ^ 40 * 2372076 * 2
def baseEnd_2372076 : Nat := 1218015136994566475441027

theorem tailTrace_2372076 : CollatzResearch.WordTrace tailWord_2372076 prefixEnd_2372076 1218015136994566475441027 := by
  unfold tailWord_2372076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43258359677190622586396041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57677812902920830115194721 43258359677190622586396041)
  ·
    refine ⟨32443769757892966939797031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43258359677190622586396041 32443769757892966939797031)
    ·
      refine ⟨48665654636839450409695547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32443769757892966939797031 48665654636839450409695547)
      ·
        refine ⟨72998481955259175614543321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48665654636839450409695547 72998481955259175614543321)
        ·
          refine ⟨54748861466444381710907491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72998481955259175614543321 54748861466444381710907491)
          ·
            refine ⟨82123292199666572566361237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54748861466444381710907491 82123292199666572566361237)
            ·
              refine ⟨3849529321859370589048183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82123292199666572566361237 3849529321859370589048183)
              ·
                refine ⟨5774293982789055883572275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849529321859370589048183 5774293982789055883572275)
                ·
                  refine ⟨8661440974183583825358413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774293982789055883572275 8661440974183583825358413)
                  ·
                    refine ⟨3248040365318843934509405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8661440974183583825358413 3248040365318843934509405)
                    ·
                      refine ⟨1218015136994566475441027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248040365318843934509405 1218015136994566475441027)
                      ·
                        rfl

theorem cell23_2372076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2372076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372076 prefixEnd_2372076 := by exact prefixLift 2372076
  have htrace : WordTrace (prefixWord ++ tailWord_2372076) baseStart_2372076 baseEnd_2372076 := by
    simpa [prefixWord, tailWord_2372076, baseEnd_2372076] using wordTrace_append hprefix tailTrace_2372076
  have hstable : (prefixWord ++ tailWord_2372076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372076).length < 2 ^ (prefixWord ++ tailWord_2372076).sum := by decide
  have hdescent : baseEnd_2372076 < baseStart_2372076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372110 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2372110 : Nat := 118140960795 + 2372110 * 2 ^ 59
def prefixEnd_2372110 : Nat := 4983230072969 + 3 ^ 40 * 2372110 * 2
def baseEnd_2372110 : Nat := 1218032595336819342415871

theorem tailTrace_2372110 : CollatzResearch.WordTrace tailWord_2372110 prefixEnd_2372110 1218032595336819342415871 := by
  unfold tailWord_2372110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814744929532258622441223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57678639624172045986353189 10814744929532258622441223)
  ·
    refine ⟨16222117394298387933661835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814744929532258622441223 16222117394298387933661835)
    ·
      refine ⟨24333176091447581900492753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222117394298387933661835 24333176091447581900492753)
      ·
        refine ⟨18249882068585686425369565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24333176091447581900492753 18249882068585686425369565)
        ·
          refine ⟨6843705775719632409513587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18249882068585686425369565 6843705775719632409513587)
          ·
            refine ⟨10265558663579448614270381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843705775719632409513587 10265558663579448614270381)
            ·
              refine ⟨3849584498842293230351393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10265558663579448614270381 3849584498842293230351393)
              ·
                refine ⟨2887188374131719922763545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849584498842293230351393 2887188374131719922763545)
                ·
                  refine ⟨2165391280598789942072659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887188374131719922763545 2165391280598789942072659)
                  ·
                    refine ⟨3248086920898184913108989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165391280598789942072659 3248086920898184913108989)
                    ·
                      refine ⟨1218032595336819342415871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248086920898184913108989 1218032595336819342415871)
                      ·
                        rfl

theorem cell23_2372110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2372110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372110 prefixEnd_2372110 := by exact prefixLift 2372110
  have htrace : WordTrace (prefixWord ++ tailWord_2372110) baseStart_2372110 baseEnd_2372110 := by
    simpa [prefixWord, tailWord_2372110, baseEnd_2372110] using wordTrace_append hprefix tailTrace_2372110
  have hstable : (prefixWord ++ tailWord_2372110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372110).length < 2 ^ (prefixWord ++ tailWord_2372110).sum := by decide
  have hdescent : baseEnd_2372110 < baseStart_2372110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372133 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_2372133 : Nat := 118140960795 + 2372133 * 2 ^ 59
def prefixEnd_2372133 : Nat := 4983230072969 + 3 ^ 40 * 2372133 * 2
def baseEnd_2372133 : Nat := 1218044405391872752428265

theorem tailTrace_2372133 : CollatzResearch.WordTrace tailWord_2372133 prefixEnd_2372133 1218044405391872752428265 := by
  unfold tailWord_2372133
  simp only [CollatzResearch.WordTrace]
  refine ⟨86518798315174743907617053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57679198876783162605078035 86518798315174743907617053)
  ·
    refine ⟨32444549368190528965356395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86518798315174743907617053 32444549368190528965356395)
    ·
      refine ⟨48666824052285793448034593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32444549368190528965356395 48666824052285793448034593)
      ·
        refine ⟨36500118039214345086025945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48666824052285793448034593 36500118039214345086025945)
        ·
          refine ⟨27375088529410758814519459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36500118039214345086025945 27375088529410758814519459)
          ·
            refine ⟨41062632794116138221779189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27375088529410758814519459 41062632794116138221779189)
            ·
              refine ⟨3849621824448387958291799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41062632794116138221779189 3849621824448387958291799)
              ·
                refine ⟨5774432736672581937437699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849621824448387958291799 5774432736672581937437699)
                ·
                  refine ⟨8661649105008872906156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774432736672581937437699 8661649105008872906156549)
                  ·
                    refine ⟨1624059207189163669904353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8661649105008872906156549 1624059207189163669904353)
                    ·
                      refine ⟨1218044405391872752428265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624059207189163669904353 1218044405391872752428265)
                      ·
                        rfl

theorem cell23_2372133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_2372133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372133 prefixEnd_2372133 := by exact prefixLift 2372133
  have htrace : WordTrace (prefixWord ++ tailWord_2372133) baseStart_2372133 baseEnd_2372133 := by
    simpa [prefixWord, tailWord_2372133, baseEnd_2372133] using wordTrace_append hprefix tailTrace_2372133
  have hstable : (prefixWord ++ tailWord_2372133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372133).length < 2 ^ (prefixWord ++ tailWord_2372133).sum := by decide
  have hdescent : baseEnd_2372133 < baseStart_2372133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372173 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2372173 : Nat := 118140960795 + 2372173 * 2 ^ 59
def prefixEnd_2372173 : Nat := 4983230072969 + 3 ^ 40 * 2372173 * 2
def baseEnd_2372173 : Nat := 135340549402005843992009

theorem tailTrace_2372173 : CollatzResearch.WordTrace tailWord_2372173 prefixEnd_2372173 135340549402005843992009 := by
  unfold tailWord_2372173
  simp only [CollatzResearch.WordTrace]
  refine ⟨86520257235029830739073173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57680171490019887159382115 86520257235029830739073173)
  ·
    refine ⟨4055637057892023315894055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86520257235029830739073173 4055637057892023315894055)
    ·
      refine ⟨6083455586838034973841083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055637057892023315894055 6083455586838034973841083)
      ·
        refine ⟨9125183380257052460761625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083455586838034973841083 9125183380257052460761625)
        ·
          refine ⟨6843887535192789345571219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9125183380257052460761625 6843887535192789345571219)
          ·
            refine ⟨10265831302789184018356829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843887535192789345571219 10265831302789184018356829)
            ·
              refine ⟨3849686738545944006883811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10265831302789184018356829 3849686738545944006883811)
              ·
                refine ⟨5774530107818916010325717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849686738545944006883811 5774530107818916010325717)
                ·
                  refine ⟨135340549402005843992009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5774530107818916010325717 135340549402005843992009)
                  ·
                    rfl

theorem cell23_2372173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2372173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372173 prefixEnd_2372173 := by exact prefixLift 2372173
  have htrace : WordTrace (prefixWord ++ tailWord_2372173) baseStart_2372173 baseEnd_2372173 := by
    simpa [prefixWord, tailWord_2372173, baseEnd_2372173] using wordTrace_append hprefix tailTrace_2372173
  have hstable : (prefixWord ++ tailWord_2372173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372173).length < 2 ^ (prefixWord ++ tailWord_2372173).sum := by decide
  have hdescent : baseEnd_2372173 < baseStart_2372173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372209 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2372209 : Nat := 118140960795 + 2372209 * 2 ^ 59
def prefixEnd_2372209 : Nat := 4983230072969 + 3 ^ 40 * 2372209 * 2
def baseEnd_2372209 : Nat := 1218083429921614455077915

theorem tailTrace_2372209 : CollatzResearch.WordTrace tailWord_2372209 prefixEnd_2372209 1218083429921614455077915 := by
  unfold tailWord_2372209
  simp only [CollatzResearch.WordTrace]
  refine ⟨86521570262899408887383681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57681046841932939258255787 86521570262899408887383681)
  ·
    refine ⟨64891177697174556665537761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86521570262899408887383681 64891177697174556665537761)
    ·
      refine ⟨48668383272880917499153321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64891177697174556665537761 48668383272880917499153321)
      ·
        refine ⟨36501287454660688124364991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48668383272880917499153321 36501287454660688124364991)
        ·
          refine ⟨54751931181991032186547487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36501287454660688124364991 54751931181991032186547487)
          ·
            refine ⟨82127896772986548279821231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54751931181991032186547487 82127896772986548279821231)
            ·
              refine ⟨123191845159479822419731847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82127896772986548279821231 123191845159479822419731847)
              ·
                refine ⟨184787767739219733629597771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123191845159479822419731847 184787767739219733629597771)
                ·
                  refine ⟨277181651608829600444396657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184787767739219733629597771 277181651608829600444396657)
                  ·
                    refine ⟨207886238706622200333297493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277181651608829600444396657 207886238706622200333297493)
                    ·
                      refine ⟨1218083429921614455077915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 207886238706622200333297493 1218083429921614455077915)
                      ·
                        rfl

theorem cell23_2372209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2372209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372209 prefixEnd_2372209 := by exact prefixLift 2372209
  have htrace : WordTrace (prefixWord ++ tailWord_2372209) baseStart_2372209 baseEnd_2372209 := by
    simpa [prefixWord, tailWord_2372209, baseEnd_2372209] using wordTrace_append hprefix tailTrace_2372209
  have hstable : (prefixWord ++ tailWord_2372209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372209).length < 2 ^ (prefixWord ++ tailWord_2372209).sum := by decide
  have hdescent : baseEnd_2372209 < baseStart_2372209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372216 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_2372216 : Nat := 118140960795 + 2372216 * 2 ^ 59
def prefixEnd_2372216 : Nat := 4983230072969 + 3 ^ 40 * 2372216 * 2
def baseEnd_2372216 : Nat := 406029008095398642563461

theorem tailTrace_2372216 : CollatzResearch.WordTrace tailWord_2372216 prefixEnd_2372216 406029008095398642563461 := by
  unfold tailWord_2372216
  simp only [CollatzResearch.WordTrace]
  refine ⟨43260912786937024541444251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57681217049249366055259001 43260912786937024541444251)
  ·
    refine ⟨64891369180405536812166377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43260912786937024541444251 64891369180405536812166377)
    ·
      refine ⟨48668526885304152609124783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64891369180405536812166377 48668526885304152609124783)
      ·
        refine ⟨73002790327956228913687175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48668526885304152609124783 73002790327956228913687175)
        ·
          refine ⟨109504185491934343370530763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73002790327956228913687175 109504185491934343370530763)
          ·
            refine ⟨164256278237901515055796145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109504185491934343370530763 164256278237901515055796145)
            ·
              refine ⟨123192208678426136291847109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164256278237901515055796145 123192208678426136291847109)
              ·
                refine ⟨23098539127204900554721333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123192208678426136291847109 23098539127204900554721333)
                ·
                  refine ⟨2165488043175459427005125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23098539127204900554721333 2165488043175459427005125)
                  ·
                    refine ⟨406029008095398642563461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165488043175459427005125 406029008095398642563461)
                    ·
                      rfl

theorem cell23_2372216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_2372216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372216 prefixEnd_2372216 := by exact prefixLift 2372216
  have htrace : WordTrace (prefixWord ++ tailWord_2372216) baseStart_2372216 baseEnd_2372216 := by
    simpa [prefixWord, tailWord_2372216, baseEnd_2372216] using wordTrace_append hprefix tailTrace_2372216
  have hstable : (prefixWord ++ tailWord_2372216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372216).length < 2 ^ (prefixWord ++ tailWord_2372216).sum := by decide
  have hdescent : baseEnd_2372216 < baseStart_2372216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372257 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2372257 : Nat := 118140960795 + 2372257 * 2 ^ 59
def prefixEnd_2372257 : Nat := 4983230072969 + 3 ^ 40 * 2372257 * 2
def baseEnd_2372257 : Nat := 1218108076993030267277695

theorem tailTrace_2372257 : CollatzResearch.WordTrace tailWord_2372257 prefixEnd_2372257 1218108076993030267277695 := by
  unfold tailWord_2372257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86523320966725513085131025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57682213977817008723420683 86523320966725513085131025)
  ·
    refine ⟨64892490725044134813848269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86523320966725513085131025 64892490725044134813848269)
    ·
      refine ⟨24334684021891550555193101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64892490725044134813848269 24334684021891550555193101)
      ·
        refine ⟨9125506508209331458197413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24334684021891550555193101 9125506508209331458197413)
        ·
          refine ⟨1711032470289249648412015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9125506508209331458197413 1711032470289249648412015)
          ·
            refine ⟨2566548705433874472618023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711032470289249648412015 2566548705433874472618023)
            ·
              refine ⟨3849823058150811708927035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566548705433874472618023 3849823058150811708927035)
              ·
                refine ⟨5774734587226217563390553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849823058150811708927035 5774734587226217563390553)
                ·
                  refine ⟨4331050940419663172542915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5774734587226217563390553 4331050940419663172542915)
                  ·
                    refine ⟨6496576410629494758814373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331050940419663172542915 6496576410629494758814373)
                    ·
                      refine ⟨1218108076993030267277695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6496576410629494758814373 1218108076993030267277695)
                      ·
                        rfl

theorem cell23_2372257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2372257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372257 prefixEnd_2372257 := by exact prefixLift 2372257
  have htrace : WordTrace (prefixWord ++ tailWord_2372257) baseStart_2372257 baseEnd_2372257 := by
    simpa [prefixWord, tailWord_2372257, baseEnd_2372257] using wordTrace_append hprefix tailTrace_2372257
  have hstable : (prefixWord ++ tailWord_2372257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372257).length < 2 ^ (prefixWord ++ tailWord_2372257).sum := by decide
  have hdescent : baseEnd_2372257 < baseStart_2372257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372300 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2372300 : Nat := 118140960795 + 2372300 * 2 ^ 59
def prefixEnd_2372300 : Nat := 4983230072969 + 3 ^ 40 * 2372300 * 2
def baseEnd_2372300 : Nat := 1218130156661173599039997

theorem tailTrace_2372300 : CollatzResearch.WordTrace tailWord_2372300 prefixEnd_2372300 1218130156661173599039997 := by
  unfold tailWord_2372300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43262444652784865714473177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57683259537046487619297569 43262444652784865714473177)
  ·
    refine ⟨32446833489588649285854883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43262444652784865714473177 32446833489588649285854883)
    ·
      refine ⟨48670250234382973928782325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32446833489588649285854883 48670250234382973928782325)
      ·
        refine ⟨4562835959473403805823343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48670250234382973928782325 4562835959473403805823343)
        ·
          refine ⟨6844253939210105708735015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562835959473403805823343 6844253939210105708735015)
          ·
            refine ⟨10266380908815158563102523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844253939210105708735015 10266380908815158563102523)
            ·
              refine ⟨15399571363222737844653785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266380908815158563102523 15399571363222737844653785)
              ·
                refine ⟨11549678522417053383490339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15399571363222737844653785 11549678522417053383490339)
                ·
                  refine ⟨17324517783625580075235509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11549678522417053383490339 17324517783625580075235509)
                  ·
                    refine ⟨1624173542214898132053329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17324517783625580075235509 1624173542214898132053329)
                    ·
                      refine ⟨1218130156661173599039997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624173542214898132053329 1218130156661173599039997)
                      ·
                        rfl

theorem cell23_2372300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2372300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372300 prefixEnd_2372300 := by exact prefixLift 2372300
  have htrace : WordTrace (prefixWord ++ tailWord_2372300) baseStart_2372300 baseEnd_2372300 := by
    simpa [prefixWord, tailWord_2372300, baseEnd_2372300] using wordTrace_append hprefix tailTrace_2372300
  have hstable : (prefixWord ++ tailWord_2372300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372300).length < 2 ^ (prefixWord ++ tailWord_2372300).sum := by decide
  have hdescent : baseEnd_2372300 < baseStart_2372300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372313 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 6, 2]
def baseStart_2372313 : Nat := 118140960795 + 2372313 * 2 ^ 59
def prefixEnd_2372313 : Nat := 4983230072969 + 3 ^ 40 * 2372313 * 2
def baseEnd_2372313 : Nat := 1218136831909682048177437

theorem tailTrace_2372313 : CollatzResearch.WordTrace tailWord_2372313 prefixEnd_2372313 1218136831909682048177437 := by
  unfold tailWord_2372313
  simp only [CollatzResearch.WordTrace]
  refine ⟨86525363454522634649169593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57683575636348423099446395 86525363454522634649169593)
  ·
    refine ⟨64894022590891975986877195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86525363454522634649169593 64894022590891975986877195)
    ·
      refine ⟨97341033886337963980315793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64894022590891975986877195 97341033886337963980315793)
      ·
        refine ⟨73005775414753472985236845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97341033886337963980315793 73005775414753472985236845)
        ·
          refine ⟨27377165780532552369463817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73005775414753472985236845 27377165780532552369463817)
          ·
            refine ⟨20532874335399414277097863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27377165780532552369463817 20532874335399414277097863)
            ·
              refine ⟨30799311503099121415646795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20532874335399414277097863 30799311503099121415646795)
              ·
                refine ⟨46198967254648682123470193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30799311503099121415646795 46198967254648682123470193)
                ·
                  refine ⟨34649225440986511592602645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46198967254648682123470193 34649225440986511592602645)
                  ·
                    refine ⟨1624182442546242730903249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34649225440986511592602645 1624182442546242730903249)
                    ·
                      refine ⟨1218136831909682048177437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624182442546242730903249 1218136831909682048177437)
                      ·
                        rfl

theorem cell23_2372313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_2372313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372313 prefixEnd_2372313 := by exact prefixLift 2372313
  have htrace : WordTrace (prefixWord ++ tailWord_2372313) baseStart_2372313 baseEnd_2372313 := by
    simpa [prefixWord, tailWord_2372313, baseEnd_2372313] using wordTrace_append hprefix tailTrace_2372313
  have hstable : (prefixWord ++ tailWord_2372313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372313).length < 2 ^ (prefixWord ++ tailWord_2372313).sum := by decide
  have hdescent : baseEnd_2372313 < baseStart_2372313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372324 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_2372324 : Nat := 118140960795 + 2372324 * 2 ^ 59
def prefixEnd_2372324 : Nat := 4983230072969 + 3 ^ 40 * 2372324 * 2
def baseEnd_2372324 : Nat := 1218142480196881505139887

theorem tailTrace_2372324 : CollatzResearch.WordTrace tailWord_2372324 prefixEnd_2372324 1218142480196881505139887 := by
  unfold tailWord_2372324
  simp only [CollatzResearch.WordTrace]
  refine ⟨43262882328741391763910013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57683843104988522351880017 43262882328741391763910013)
  ·
    refine ⟨16223580873278021911466255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43262882328741391763910013 16223580873278021911466255)
    ·
      refine ⟨24335371309917032867199383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16223580873278021911466255 24335371309917032867199383)
      ·
        refine ⟨36503056964875549300799075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24335371309917032867199383 36503056964875549300799075)
        ·
          refine ⟨54754585447313323951198613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36503056964875549300799075 54754585447313323951198613)
          ·
            refine ⟨2566621192842812060212435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54754585447313323951198613 2566621192842812060212435)
            ·
              refine ⟨3849931789264218090318653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566621192842812060212435 3849931789264218090318653)
              ·
                refine ⟨1443724420974081783869495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849931789264218090318653 1443724420974081783869495)
                ·
                  refine ⟨2165586631461122675804243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443724420974081783869495 2165586631461122675804243)
                  ·
                    refine ⟨3248379947191684013706365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165586631461122675804243 3248379947191684013706365)
                    ·
                      refine ⟨1218142480196881505139887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248379947191684013706365 1218142480196881505139887)
                      ·
                        rfl

theorem cell23_2372324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_2372324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372324 prefixEnd_2372324 := by exact prefixLift 2372324
  have htrace : WordTrace (prefixWord ++ tailWord_2372324) baseStart_2372324 baseEnd_2372324 := by
    simpa [prefixWord, tailWord_2372324, baseEnd_2372324] using wordTrace_append hprefix tailTrace_2372324
  have hstable : (prefixWord ++ tailWord_2372324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372324).length < 2 ^ (prefixWord ++ tailWord_2372324).sum := by decide
  have hdescent : baseEnd_2372324 < baseStart_2372324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372350 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2372350 : Nat := 118140960795 + 2372350 * 2 ^ 59
def prefixEnd_2372350 : Nat := 4983230072969 + 3 ^ 40 * 2372350 * 2
def baseEnd_2372350 : Nat := 1218155830693898403414767

theorem tailTrace_2372350 : CollatzResearch.WordTrace tailWord_2372350 prefixEnd_2372350 1218155830693898403414767 := by
  unfold tailWord_2372350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815839119423573746033313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57684475303592393312177669 10815839119423573746033313)
  ·
    refine ⟨8111879339567680309524985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10815839119423573746033313 8111879339567680309524985)
    ·
      refine ⟨6083909504675760232143739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8111879339567680309524985 6083909504675760232143739)
      ·
        refine ⟨9125864257013640348215609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083909504675760232143739 9125864257013640348215609)
        ·
          refine ⟨6844398192760230261161707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9125864257013640348215609 6844398192760230261161707)
          ·
            refine ⟨10266597289140345391742561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844398192760230261161707 10266597289140345391742561)
            ·
              refine ⟨7699947966855259043806921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10266597289140345391742561 7699947966855259043806921)
              ·
                refine ⟨5774960975141444282855191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7699947966855259043806921 5774960975141444282855191)
                ·
                  refine ⟨8662441462712166424282787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774960975141444282855191 8662441462712166424282787)
                  ·
                    refine ⟨12993662194068249636424181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8662441462712166424282787 12993662194068249636424181)
                    ·
                      refine ⟨1218155830693898403414767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12993662194068249636424181 1218155830693898403414767)
                      ·
                        rfl

theorem cell23_2372350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2372350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372350 prefixEnd_2372350 := by exact prefixLift 2372350
  have htrace : WordTrace (prefixWord ++ tailWord_2372350) baseStart_2372350 baseEnd_2372350 := by
    simpa [prefixWord, tailWord_2372350, baseEnd_2372350] using wordTrace_append hprefix tailTrace_2372350
  have hstable : (prefixWord ++ tailWord_2372350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372350).length < 2 ^ (prefixWord ++ tailWord_2372350).sum := by decide
  have hdescent : baseEnd_2372350 < baseStart_2372350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372363 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3]
def baseStart_2372363 : Nat := 118140960795 + 2372363 * 2 ^ 59
def prefixEnd_2372363 : Nat := 4983230072969 + 3 ^ 40 * 2372363 * 2
def baseEnd_2372363 : Nat := 1218162505942406852552207

theorem tailTrace_2372363 : CollatzResearch.WordTrace tailWord_2372363 prefixEnd_2372363 1218162505942406852552207 := by
  unfold tailWord_2372363
  simp only [CollatzResearch.WordTrace]
  refine ⟨86527187104341493188489743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57684791402894328792326495 86527187104341493188489743)
  ·
    refine ⟨129790780656512239782734615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86527187104341493188489743 129790780656512239782734615)
    ·
      refine ⟨194686170984768359674101923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129790780656512239782734615 194686170984768359674101923)
      ·
        refine ⟨292029256477152539511152885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194686170984768359674101923 292029256477152539511152885)
        ·
          refine ⟨27377742794733050579170583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292029256477152539511152885 27377742794733050579170583)
          ·
            refine ⟨41066614192099575868755875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27377742794733050579170583 41066614192099575868755875)
            ·
              refine ⟨61599921288149363803133813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41066614192099575868755875 61599921288149363803133813)
              ·
                refine ⟨5774992620764002856543795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61599921288149363803133813 5774992620764002856543795)
                ·
                  refine ⟨8662488931146004284815693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774992620764002856543795 8662488931146004284815693)
                  ·
                    refine ⟨3248433349179751606805885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8662488931146004284815693 3248433349179751606805885)
                    ·
                      refine ⟨1218162505942406852552207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248433349179751606805885 1218162505942406852552207)
                      ·
                        rfl

theorem cell23_2372363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].length) (baseStart_2372363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372363 prefixEnd_2372363 := by exact prefixLift 2372363
  have htrace : WordTrace (prefixWord ++ tailWord_2372363) baseStart_2372363 baseEnd_2372363 := by
    simpa [prefixWord, tailWord_2372363, baseEnd_2372363] using wordTrace_append hprefix tailTrace_2372363
  have hstable : (prefixWord ++ tailWord_2372363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372363).length < 2 ^ (prefixWord ++ tailWord_2372363).sum := by decide
  have hdescent : baseEnd_2372363 < baseStart_2372363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372380 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2372380 : Nat := 118140960795 + 2372380 * 2 ^ 59
def prefixEnd_2372380 : Nat := 4983230072969 + 3 ^ 40 * 2372380 * 2
def baseEnd_2372380 : Nat := 1218171235113533286039629

theorem tailTrace_2372380 : CollatzResearch.WordTrace tailWord_2372380 prefixEnd_2372380 1218171235113533286039629 := by
  unfold tailWord_2372380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43263903572639952545929297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57685204763519936727905729 43263903572639952545929297)
  ·
    refine ⟨32447927679479964409446973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43263903572639952545929297 32447927679479964409446973)
    ·
      refine ⟨12167972879804986653542615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32447927679479964409446973 12167972879804986653542615)
      ·
        refine ⟨18251959319707479980313923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12167972879804986653542615 18251959319707479980313923)
        ·
          refine ⟨27377938979561219970470885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18251959319707479980313923 27377938979561219970470885)
          ·
            refine ⟨5133363558667728744463291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27377938979561219970470885 5133363558667728744463291)
            ·
              refine ⟨7700045338001593116694937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133363558667728744463291 7700045338001593116694937)
              ·
                refine ⟨5775034003501194837521203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7700045338001593116694937 5775034003501194837521203)
                ·
                  refine ⟨8662551005251792256281805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775034003501194837521203 8662551005251792256281805)
                  ·
                    refine ⟨3248456626969422096105677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8662551005251792256281805 3248456626969422096105677)
                    ·
                      refine ⟨1218171235113533286039629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248456626969422096105677 1218171235113533286039629)
                      ·
                        rfl

theorem cell23_2372380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2372380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372380 prefixEnd_2372380 := by exact prefixLift 2372380
  have htrace : WordTrace (prefixWord ++ tailWord_2372380) baseStart_2372380 baseEnd_2372380 := by
    simpa [prefixWord, tailWord_2372380, baseEnd_2372380] using wordTrace_append hprefix tailTrace_2372380
  have hstable : (prefixWord ++ tailWord_2372380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372380).length < 2 ^ (prefixWord ++ tailWord_2372380).sum := by decide
  have hdescent : baseEnd_2372380 < baseStart_2372380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372398 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2372398 : Nat := 118140960795 + 2372398 * 2 ^ 59
def prefixEnd_2372398 : Nat := 4983230072969 + 3 ^ 40 * 2372398 * 2
def baseEnd_2372398 : Nat := 1218180477765314215614547

theorem tailTrace_2372398 : CollatzResearch.WordTrace tailWord_2372398 prefixEnd_2372398 1218180477765314215614547 := by
  unfold tailWord_2372398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816057957401836770751731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57685642439476462777342565 10816057957401836770751731)
  ·
    refine ⟨16224086936102755156127597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10816057957401836770751731 16224086936102755156127597)
    ·
      refine ⟨6084032601038533183547849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16224086936102755156127597 6084032601038533183547849)
      ·
        refine ⟨4563024450778899887660887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6084032601038533183547849 4563024450778899887660887)
        ·
          refine ⟨6844536676168349831491331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563024450778899887660887 6844536676168349831491331)
          ·
            refine ⟨10266805014252524747236997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844536676168349831491331 10266805014252524747236997)
            ·
              refine ⟨1925025940172348390106937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10266805014252524747236997 1925025940172348390106937)
              ·
                refine ⟨1443769455129261292580203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925025940172348390106937 1443769455129261292580203)
                ·
                  refine ⟨2165654182693891938870305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443769455129261292580203 2165654182693891938870305)
                  ·
                    refine ⟨1624240637020418954152729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165654182693891938870305 1624240637020418954152729)
                    ·
                      refine ⟨1218180477765314215614547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624240637020418954152729 1218180477765314215614547)
                      ·
                        rfl

theorem cell23_2372398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2372398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372398 prefixEnd_2372398 := by exact prefixLift 2372398
  have htrace : WordTrace (prefixWord ++ tailWord_2372398) baseStart_2372398 baseEnd_2372398 := by
    simpa [prefixWord, tailWord_2372398, baseEnd_2372398] using wordTrace_append hprefix tailTrace_2372398
  have hstable : (prefixWord ++ tailWord_2372398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372398).length < 2 ^ (prefixWord ++ tailWord_2372398).sum := by decide
  have hdescent : baseEnd_2372398 < baseStart_2372398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372403 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_2372403 : Nat := 118140960795 + 2372403 * 2 ^ 59
def prefixEnd_2372403 : Nat := 4983230072969 + 3 ^ 40 * 2372403 * 2
def baseEnd_2372403 : Nat := 1218183045168586696052023

theorem tailTrace_2372403 : CollatzResearch.WordTrace tailWord_2372403 prefixEnd_2372403 1218183045168586696052023 := by
  unfold tailWord_2372403
  simp only [CollatzResearch.WordTrace]
  refine ⟨86528646024196580019945863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57685764016131053346630575 86528646024196580019945863)
  ·
    refine ⟨129792969036294870029918795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86528646024196580019945863 129792969036294870029918795)
    ·
      refine ⟨194689453554442305044878193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129792969036294870029918795 194689453554442305044878193)
      ·
        refine ⟨146017090165831728783658645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194689453554442305044878193 146017090165831728783658645)
        ·
          refine ⟨6844551101523362286733999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146017090165831728783658645 6844551101523362286733999)
          ·
            refine ⟨10266826652285043430100999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844551101523362286733999 10266826652285043430100999)
            ·
              refine ⟨15400239978427565145151499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266826652285043430100999 15400239978427565145151499)
              ·
                refine ⟨23100359967641347717727249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15400239978427565145151499 23100359967641347717727249)
                ·
                  refine ⟨17325269975731010788295437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23100359967641347717727249 17325269975731010788295437)
                  ·
                    refine ⟨6496976240899129045610789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17325269975731010788295437 6496976240899129045610789)
                    ·
                      refine ⟨1218183045168586696052023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6496976240899129045610789 1218183045168586696052023)
                      ·
                        rfl

theorem cell23_2372403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_2372403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372403 prefixEnd_2372403 := by exact prefixLift 2372403
  have htrace : WordTrace (prefixWord ++ tailWord_2372403) baseStart_2372403 baseEnd_2372403 := by
    simpa [prefixWord, tailWord_2372403, baseEnd_2372403] using wordTrace_append hprefix tailTrace_2372403
  have hstable : (prefixWord ++ tailWord_2372403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372403).length < 2 ^ (prefixWord ++ tailWord_2372403).sum := by decide
  have hdescent : baseEnd_2372403 < baseStart_2372403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2372423 : Nat := 118140960795 + 2372423 * 2 ^ 59
def prefixEnd_2372423 : Nat := 4983230072969 + 3 ^ 40 * 2372423 * 2
def baseEnd_2372423 : Nat := 1218193314781676617801931

theorem tailTrace_2372423 : CollatzResearch.WordTrace tailWord_2372423 prefixEnd_2372423 1218193314781676617801931 := by
  unfold tailWord_2372423
  simp only [CollatzResearch.WordTrace]
  refine ⟨86529375484124123435673923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57686250322749415623782615 86529375484124123435673923)
  ·
    refine ⟨129794063226186185153510885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86529375484124123435673923 129794063226186185153510885)
    ·
      refine ⟨24336386854909909716283291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129794063226186185153510885 24336386854909909716283291)
      ·
        refine ⟨36504580282364864574424937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24336386854909909716283291 36504580282364864574424937)
        ·
          refine ⟨27378435211773648430818703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36504580282364864574424937 27378435211773648430818703)
          ·
            refine ⟨41067652817660472646228055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27378435211773648430818703 41067652817660472646228055)
            ·
              refine ⟨61601479226490708969342083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41067652817660472646228055 61601479226490708969342083)
              ·
                refine ⟨92402218839736063454013125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61601479226490708969342083 92402218839736063454013125)
                ·
                  refine ⟨17325416032450511897627461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92402218839736063454013125 17325416032450511897627461)
                  ·
                    refine ⟨3248515506084470980805149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17325416032450511897627461 3248515506084470980805149)
                    ·
                      refine ⟨1218193314781676617801931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248515506084470980805149 1218193314781676617801931)
                      ·
                        rfl

theorem cell23_2372423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2372423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372423 prefixEnd_2372423 := by exact prefixLift 2372423
  have htrace : WordTrace (prefixWord ++ tailWord_2372423) baseStart_2372423 baseEnd_2372423 := by
    simpa [prefixWord, tailWord_2372423, baseEnd_2372423] using wordTrace_append hprefix tailTrace_2372423
  have hstable : (prefixWord ++ tailWord_2372423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372423).length < 2 ^ (prefixWord ++ tailWord_2372423).sum := by decide
  have hdescent : baseEnd_2372423 < baseStart_2372423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372437 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2372437 : Nat := 118140960795 + 2372437 * 2 ^ 59
def prefixEnd_2372437 : Nat := 4983230072969 + 3 ^ 40 * 2372437 * 2
def baseEnd_2372437 : Nat := 1218200503510839563026867

theorem tailTrace_2372437 : CollatzResearch.WordTrace tailWord_2372437 prefixEnd_2372437 1218200503510839563026867 := by
  unfold tailWord_2372437
  simp only [CollatzResearch.WordTrace]
  refine ⟨86529886106073403826683565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57686590737382269217789043 86529886106073403826683565)
  ·
    refine ⟨32448707289777526435006337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86529886106073403826683565 32448707289777526435006337)
    ·
      refine ⟨24336530467333144826254753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32448707289777526435006337 24336530467333144826254753)
      ·
        refine ⟨18252397850499858619691065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24336530467333144826254753 18252397850499858619691065)
        ·
          refine ⟨13689298387874893964768299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18252397850499858619691065 13689298387874893964768299)
          ·
            refine ⟨20533947581812340947152449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13689298387874893964768299 20533947581812340947152449)
            ·
              refine ⟨15400460686359255710364337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20533947581812340947152449 15400460686359255710364337)
              ·
                refine ⟨11550345514769441782773253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15400460686359255710364337 11550345514769441782773253)
                ·
                  refine ⟨2165689784019270334269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11550345514769441782773253 2165689784019270334269985)
                  ·
                    refine ⟨1624267338014452750702489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165689784019270334269985 1624267338014452750702489)
                    ·
                      refine ⟨1218200503510839563026867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624267338014452750702489 1218200503510839563026867)
                      ·
                        rfl

theorem cell23_2372437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2372437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372437 prefixEnd_2372437 := by exact prefixLift 2372437
  have htrace : WordTrace (prefixWord ++ tailWord_2372437) baseStart_2372437 baseEnd_2372437 := by
    simpa [prefixWord, tailWord_2372437, baseEnd_2372437] using wordTrace_append hprefix tailTrace_2372437
  have hstable : (prefixWord ++ tailWord_2372437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372437).length < 2 ^ (prefixWord ++ tailWord_2372437).sum := by decide
  have hdescent : baseEnd_2372437 < baseStart_2372437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372460 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 5]
def baseStart_2372460 : Nat := 118140960795 + 2372460 * 2 ^ 59
def prefixEnd_2372460 : Nat := 4983230072969 + 3 ^ 40 * 2372460 * 2
def baseEnd_2372460 : Nat := 135356923729543663671029

theorem tailTrace_2372460 : CollatzResearch.WordTrace tailWord_2372460 prefixEnd_2372460 135356923729543663671029 := by
  unfold tailWord_2372460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265362492495039377385417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57687149989993385836513889 43265362492495039377385417)
  ·
    refine ⟨32449021869371279533039063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43265362492495039377385417 32449021869371279533039063)
    ·
      refine ⟨48673532804056919299558595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32449021869371279533039063 48673532804056919299558595)
      ·
        refine ⟨73010299206085378949337893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48673532804056919299558595 73010299206085378949337893)
        ·
          refine ⟨13689431101141008553000855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73010299206085378949337893 13689431101141008553000855)
          ·
            refine ⟨20534146651711512829501283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13689431101141008553000855 20534146651711512829501283)
            ·
              refine ⟨30801219977567269244251925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20534146651711512829501283 30801219977567269244251925)
              ·
                refine ⟨1443807186448465745824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30801219977567269244251925 1443807186448465745824309)
                ·
                  refine ⟨135356923729543663671029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1443807186448465745824309 135356923729543663671029)
                  ·
                    rfl

theorem cell23_2372460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_2372460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372460 prefixEnd_2372460 := by exact prefixLift 2372460
  have htrace : WordTrace (prefixWord ++ tailWord_2372460) baseStart_2372460 baseEnd_2372460 := by
    simpa [prefixWord, tailWord_2372460, baseEnd_2372460] using wordTrace_append hprefix tailTrace_2372460
  have hstable : (prefixWord ++ tailWord_2372460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372460).length < 2 ^ (prefixWord ++ tailWord_2372460).sum := by decide
  have hdescent : baseEnd_2372460 < baseStart_2372460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372473 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_2372473 : Nat := 118140960795 + 2372473 * 2 ^ 59
def prefixEnd_2372473 : Nat := 4983230072969 + 3 ^ 40 * 2372473 * 2
def baseEnd_2372473 : Nat := 406072996271467140725567

theorem tailTrace_2372473 : CollatzResearch.WordTrace tailWord_2372473 prefixEnd_2372473 406072996271467140725567 := by
  unfold tailWord_2372473
  simp only [CollatzResearch.WordTrace]
  refine ⟨86531199133942981974994073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57687466089295321316662715 86531199133942981974994073)
  ·
    refine ⟨64898399350457236481245555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86531199133942981974994073 64898399350457236481245555)
    ·
      refine ⟨97347599025685854721868333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64898399350457236481245555 97347599025685854721868333)
      ·
        refine ⟨36505349634632195520700625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97347599025685854721868333 36505349634632195520700625)
        ·
          refine ⟨27379012225974146640525469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36505349634632195520700625 27379012225974146640525469)
          ·
            refine ⟨10267129584740304990197051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27379012225974146640525469 10267129584740304990197051)
            ·
              refine ⟨15400694377110457485295577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10267129584740304990197051 15400694377110457485295577)
              ·
                refine ⟨11550520782832843113971683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15400694377110457485295577 11550520782832843113971683)
                ·
                  refine ⟨17325781174249264670957525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11550520782832843113971683 17325781174249264670957525)
                  ·
                    refine ⟨406072996271467140725567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17325781174249264670957525 406072996271467140725567)
                    ·
                      rfl

theorem cell23_2372473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_2372473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372473 prefixEnd_2372473 := by exact prefixLift 2372473
  have htrace : WordTrace (prefixWord ++ tailWord_2372473) baseStart_2372473 baseEnd_2372473 := by
    simpa [prefixWord, tailWord_2372473, baseEnd_2372473] using wordTrace_append hprefix tailTrace_2372473
  have hstable : (prefixWord ++ tailWord_2372473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372473).length < 2 ^ (prefixWord ++ tailWord_2372473).sum := by decide
  have hdescent : baseEnd_2372473 < baseStart_2372473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372490 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_2372490 : Nat := 118140960795 + 2372490 * 2 ^ 59
def prefixEnd_2372490 : Nat := 4983230072969 + 3 ^ 40 * 2372490 * 2
def baseEnd_2372490 : Nat := 406075905995175951888041

theorem tailTrace_2372490 : CollatzResearch.WordTrace tailWord_2372490 prefixEnd_2372490 406075905995175951888041 := by
  unfold tailWord_2372490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632954793720348469590731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57687879449920929252241949 21632954793720348469590731)
  ·
    refine ⟨32449432190580522704386097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21632954793720348469590731 32449432190580522704386097)
    ·
      refine ⟨24337074142935392028289573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32449432190580522704386097 24337074142935392028289573)
      ·
        refine ⟨4563201401800386005304295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24337074142935392028289573 4563201401800386005304295)
        ·
          refine ⟨6844802102700579007956443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563201401800386005304295 6844802102700579007956443)
          ·
            refine ⟨10267203154050868511934665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844802102700579007956443 10267203154050868511934665)
            ·
              refine ⟨7700402365538151383950999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10267203154050868511934665 7700402365538151383950999)
              ·
                refine ⟨11550603548307227075926499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7700402365538151383950999 11550603548307227075926499)
                ·
                  refine ⟨17325905322460840613889749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11550603548307227075926499 17325905322460840613889749)
                  ·
                    refine ⟨406075905995175951888041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17325905322460840613889749 406075905995175951888041)
                    ·
                      rfl

theorem cell23_2372490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_2372490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372490 prefixEnd_2372490 := by exact prefixLift 2372490
  have htrace : WordTrace (prefixWord ++ tailWord_2372490) baseStart_2372490 baseEnd_2372490 := by
    simpa [prefixWord, tailWord_2372490, baseEnd_2372490] using wordTrace_append hprefix tailTrace_2372490
  have hstable : (prefixWord ++ tailWord_2372490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372490).length < 2 ^ (prefixWord ++ tailWord_2372490).sum := by decide
  have hdescent : baseEnd_2372490 < baseStart_2372490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372500 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2372500 : Nat := 118140960795 + 2372500 * 2 ^ 59
def prefixEnd_2372500 : Nat := 4983230072969 + 3 ^ 40 * 2372500 * 2
def baseEnd_2372500 : Nat := 1218232852792072816539077

theorem tailTrace_2372500 : CollatzResearch.WordTrace tailWord_2372500 prefixEnd_2372500 1218232852792072816539077 := by
  unfold tailWord_2372500
  simp only [CollatzResearch.WordTrace]
  refine ⟨43266091952422582793113477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57688122603230110390817969 43266091952422582793113477)
  ·
    refine ⟨8112392241079234273708777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43266091952422582793113477 8112392241079234273708777)
    ·
      refine ⟨6084294180809425705281583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8112392241079234273708777 6084294180809425705281583)
      ·
        refine ⟨9126441271214138557922375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6084294180809425705281583 9126441271214138557922375)
        ·
          refine ⟨13689661906821207836883563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9126441271214138557922375 13689661906821207836883563)
          ·
            refine ⟨20534492860231811755325345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13689661906821207836883563 20534492860231811755325345)
            ·
              refine ⟨15400869645173858816494009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20534492860231811755325345 15400869645173858816494009)
              ·
                refine ⟨11550652233880394112370507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15400869645173858816494009 11550652233880394112370507)
                ·
                  refine ⟨17325978350820591168555761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11550652233880394112370507 17325978350820591168555761)
                  ·
                    refine ⟨12994483763115443376416821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17325978350820591168555761 12994483763115443376416821)
                    ·
                      refine ⟨1218232852792072816539077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12994483763115443376416821 1218232852792072816539077)
                      ·
                        rfl

theorem cell23_2372500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2372500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372500 prefixEnd_2372500 := by exact prefixLift 2372500
  have htrace : WordTrace (prefixWord ++ tailWord_2372500) baseStart_2372500 baseEnd_2372500 := by
    simpa [prefixWord, tailWord_2372500, baseEnd_2372500] using wordTrace_append hprefix tailTrace_2372500
  have hstable : (prefixWord ++ tailWord_2372500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372500).length < 2 ^ (prefixWord ++ tailWord_2372500).sum := by decide
  have hdescent : baseEnd_2372500 < baseStart_2372500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372577 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_2372577 : Nat := 118140960795 + 2372577 * 2 ^ 59
def prefixEnd_2372577 : Nat := 4983230072969 + 3 ^ 40 * 2372577 * 2
def baseEnd_2372577 : Nat := 1218272390802469015276223

theorem tailTrace_2372577 : CollatzResearch.WordTrace tailWord_2372577 prefixEnd_2372577 1218272390802469015276223 := by
  unfold tailWord_2372577
  simp only [CollatzResearch.WordTrace]
  refine ⟨86534992325566207736779985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57689994883710805157853323 86534992325566207736779985)
  ·
    refine ⟨64901244244174655802584989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86534992325566207736779985 64901244244174655802584989)
    ·
      refine ⟨24337966591565495925969371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64901244244174655802584989 24337966591565495925969371)
      ·
        refine ⟨36506949887348243888954057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24337966591565495925969371 36506949887348243888954057)
        ·
          refine ⟨27380212415511182916715543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36506949887348243888954057 27380212415511182916715543)
          ·
            refine ⟨41070318623266774375073315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27380212415511182916715543 41070318623266774375073315)
            ·
              refine ⟨61605477934900161562609973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41070318623266774375073315 61605477934900161562609973)
              ·
                refine ⟨5775513556396890146494685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61605477934900161562609973 5775513556396890146494685)
                ·
                  refine ⟨2165817583648833804935507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5775513556396890146494685 2165817583648833804935507)
                  ·
                    refine ⟨3248726375473250707403261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165817583648833804935507 3248726375473250707403261)
                    ·
                      refine ⟨1218272390802469015276223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248726375473250707403261 1218272390802469015276223)
                      ·
                        rfl

theorem cell23_2372577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_2372577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372577 prefixEnd_2372577 := by exact prefixLift 2372577
  have htrace : WordTrace (prefixWord ++ tailWord_2372577) baseStart_2372577 baseEnd_2372577 := by
    simpa [prefixWord, tailWord_2372577, baseEnd_2372577] using wordTrace_append hprefix tailTrace_2372577
  have hstable : (prefixWord ++ tailWord_2372577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372577).length < 2 ^ (prefixWord ++ tailWord_2372577).sum := by decide
  have hdescent : baseEnd_2372577 < baseStart_2372577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372604 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_2372604 : Nat := 118140960795 + 2372604 * 2 ^ 59
def prefixEnd_2372604 : Nat := 4983230072969 + 3 ^ 40 * 2372604 * 2
def baseEnd_2372604 : Nat := 1218286254780140409638599

theorem tailTrace_2372604 : CollatzResearch.WordTrace tailWord_2372604 prefixEnd_2372604 1218286254780140409638599 := by
  unfold tailWord_2372604
  simp only [CollatzResearch.WordTrace]
  refine ⟨43267988548234195674006433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57690651397645594232008577 43267988548234195674006433)
  ·
    refine ⟨32450991411175646755504825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43267988548234195674006433 32450991411175646755504825)
    ·
      refine ⟨24338243558381735066628619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32450991411175646755504825 24338243558381735066628619)
      ·
        refine ⟨36507365337572602599942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24338243558381735066628619 36507365337572602599942929)
        ·
          refine ⟨27380524003179451949957197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36507365337572602599942929 27380524003179451949957197)
          ·
            refine ⟨10267696501192294481233949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27380524003179451949957197 10267696501192294481233949)
            ·
              refine ⟨3850386187947110430462731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10267696501192294481233949 3850386187947110430462731)
              ·
                refine ⟨5775579281920665645694097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850386187947110430462731 5775579281920665645694097)
                ·
                  refine ⟨4331684461440499234270573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775579281920665645694097 4331684461440499234270573)
                  ·
                    refine ⟨1624381673040187212851465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4331684461440499234270573 1624381673040187212851465)
                    ·
                      refine ⟨1218286254780140409638599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624381673040187212851465 1218286254780140409638599)
                      ·
                        rfl

theorem cell23_2372604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_2372604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372604 prefixEnd_2372604 := by exact prefixLift 2372604
  have htrace : WordTrace (prefixWord ++ tailWord_2372604) baseStart_2372604 baseEnd_2372604 := by
    simpa [prefixWord, tailWord_2372604, baseEnd_2372604] using wordTrace_append hprefix tailTrace_2372604
  have hstable : (prefixWord ++ tailWord_2372604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372604).length < 2 ^ (prefixWord ++ tailWord_2372604).sum := by decide
  have hdescent : baseEnd_2372604 < baseStart_2372604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372644 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_2372644 : Nat := 118140960795 + 2372644 * 2 ^ 59
def prefixEnd_2372644 : Nat := 4983230072969 + 3 ^ 40 * 2372644 * 2
def baseEnd_2372644 : Nat := 406102264668773417712805

theorem tailTrace_2372644 : CollatzResearch.WordTrace tailWord_2372644 prefixEnd_2372644 406102264668773417712805 := by
  unfold tailWord_2372644
  simp only [CollatzResearch.WordTrace]
  refine ⟨43268718008161739089734493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57691624010882318786312657 43268718008161739089734493)
  ·
    refine ⟨16225769253060652158650435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43268718008161739089734493 16225769253060652158650435)
    ·
      refine ⟨24338653879590978237975653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16225769253060652158650435 24338653879590978237975653)
      ·
        refine ⟨4563497602423308419620435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24338653879590978237975653 4563497602423308419620435)
        ·
          refine ⟨6845246403634962629430653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563497602423308419620435 6845246403634962629430653)
          ·
            refine ⟨2566967401363110986036495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6845246403634962629430653 2566967401363110986036495)
            ·
              refine ⟨3850451102044666479054743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566967401363110986036495 3850451102044666479054743)
              ·
                refine ⟨5775676653066999718582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850451102044666479054743 5775676653066999718582115)
                ·
                  refine ⟨8663514979600499577873173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775676653066999718582115 8663514979600499577873173)
                  ·
                    refine ⟨406102264668773417712805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8663514979600499577873173 406102264668773417712805)
                    ·
                      rfl

theorem cell23_2372644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_2372644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372644 prefixEnd_2372644 := by exact prefixLift 2372644
  have htrace : WordTrace (prefixWord ++ tailWord_2372644) baseStart_2372644 baseEnd_2372644 := by
    simpa [prefixWord, tailWord_2372644, baseEnd_2372644] using wordTrace_append hprefix tailTrace_2372644
  have hstable : (prefixWord ++ tailWord_2372644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372644).length < 2 ^ (prefixWord ++ tailWord_2372644).sum := by decide
  have hdescent : baseEnd_2372644 < baseStart_2372644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372668 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_2372668 : Nat := 118140960795 + 2372668 * 2 ^ 59
def prefixEnd_2372668 : Nat := 4983230072969 + 3 ^ 40 * 2372668 * 2
def baseEnd_2372668 : Nat := 1218319117542028159238305

theorem tailTrace_2372668 : CollatzResearch.WordTrace tailWord_2372668 prefixEnd_2372668 1218319117542028159238305 := by
  unfold tailWord_2372668
  simp only [CollatzResearch.WordTrace]
  refine ⟨43269155684118265139171329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57692207578824353518895105 43269155684118265139171329)
  ·
    refine ⟨32451866763088698854378497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43269155684118265139171329 32451866763088698854378497)
    ·
      refine ⟨24338900072316524140783873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32451866763088698854378497 24338900072316524140783873)
      ·
        refine ⟨18254175054237393105587905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24338900072316524140783873 18254175054237393105587905)
        ·
          refine ⟨13690631290678044829190929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18254175054237393105587905 13690631290678044829190929)
          ·
            refine ⟨10267973468008533621893197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13690631290678044829190929 10267973468008533621893197)
            ·
              refine ⟨3850490050503200108209949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10267973468008533621893197 3850490050503200108209949)
              ·
                refine ⟨1443933768938700040578731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3850490050503200108209949 1443933768938700040578731)
                ·
                  refine ⟨2165900653408050060868097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443933768938700040578731 2165900653408050060868097)
                  ·
                    refine ⟨1624425490056037545651073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165900653408050060868097 1624425490056037545651073)
                    ·
                      refine ⟨1218319117542028159238305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624425490056037545651073 1218319117542028159238305)
                      ·
                        rfl

theorem cell23_2372668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_2372668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372668 prefixEnd_2372668 := by exact prefixLift 2372668
  have htrace : WordTrace (prefixWord ++ tailWord_2372668) baseStart_2372668 baseEnd_2372668 := by
    simpa [prefixWord, tailWord_2372668, baseEnd_2372668] using wordTrace_append hprefix tailTrace_2372668
  have hstable : (prefixWord ++ tailWord_2372668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372668).length < 2 ^ (prefixWord ++ tailWord_2372668).sum := by decide
  have hdescent : baseEnd_2372668 < baseStart_2372668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372680 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2372680 : Nat := 118140960795 + 2372680 * 2 ^ 59
def prefixEnd_2372680 : Nat := 4983230072969 + 3 ^ 40 * 2372680 * 2
def baseEnd_2372680 : Nat := 1218325279309882112288249

theorem tailTrace_2372680 : CollatzResearch.WordTrace tailWord_2372680 prefixEnd_2372680 1218325279309882112288249 := by
  unfold tailWord_2372680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43269374522096528163889747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57692499362795370885186329 43269374522096528163889747)
  ·
    refine ⟨64904061783144792245834621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43269374522096528163889747 64904061783144792245834621)
    ·
      refine ⟨24339023168679297092187983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64904061783144792245834621 24339023168679297092187983)
      ·
        refine ⟨36508534753018945638281975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24339023168679297092187983 36508534753018945638281975)
        ·
          refine ⟨54762802129528418457422963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36508534753018945638281975 54762802129528418457422963)
          ·
            refine ⟨82144203194292627686134445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54762802129528418457422963 82144203194292627686134445)
            ·
              refine ⟨30804076197859735382300417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82144203194292627686134445 30804076197859735382300417)
              ·
                refine ⟨23103057148394801536725313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30804076197859735382300417 23103057148394801536725313)
                ·
                  refine ⟨17327292861296101152543985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23103057148394801536725313 17327292861296101152543985)
                  ·
                    refine ⟨12995469645972075864407989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17327292861296101152543985 12995469645972075864407989)
                    ·
                      refine ⟨1218325279309882112288249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12995469645972075864407989 1218325279309882112288249)
                      ·
                        rfl

theorem cell23_2372680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2372680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372680 prefixEnd_2372680 := by exact prefixLift 2372680
  have htrace : WordTrace (prefixWord ++ tailWord_2372680) baseStart_2372680 baseEnd_2372680 := by
    simpa [prefixWord, tailWord_2372680, baseEnd_2372680] using wordTrace_append hprefix tailTrace_2372680
  have hstable : (prefixWord ++ tailWord_2372680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372680).length < 2 ^ (prefixWord ++ tailWord_2372680).sum := by decide
  have hdescent : baseEnd_2372680 < baseStart_2372680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372684 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2372684 : Nat := 118140960795 + 2372684 * 2 ^ 59
def prefixEnd_2372684 : Nat := 4983230072969 + 3 ^ 40 * 2372684 * 2
def baseEnd_2372684 : Nat := 1218327333232500096638231

theorem tailTrace_2372684 : CollatzResearch.WordTrace tailWord_2372684 prefixEnd_2372684 1218327333232500096638231 := by
  unfold tailWord_2372684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43269447468089282505462553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57692596624119043340616737 43269447468089282505462553)
  ·
    refine ⟨32452085601066961879096915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43269447468089282505462553 32452085601066961879096915)
    ·
      refine ⟨48678128401600442818645373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32452085601066961879096915 48678128401600442818645373)
      ·
        refine ⟨18254298150600166056992015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48678128401600442818645373 18254298150600166056992015)
        ·
          refine ⟨27381447225900249085488023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254298150600166056992015 27381447225900249085488023)
          ·
            refine ⟨41072170838850373628232035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27381447225900249085488023 41072170838850373628232035)
            ·
              refine ⟨61608256258275560442348053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41072170838850373628232035 61608256258275560442348053)
              ·
                refine ⟨2887887012106666895735065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61608256258275560442348053 2887887012106666895735065)
                ·
                  refine ⟨2165915259080000171801299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887887012106666895735065 2165915259080000171801299)
                  ·
                    refine ⟨3248872888620000257701949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165915259080000171801299 3248872888620000257701949)
                    ·
                      refine ⟨1218327333232500096638231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3248872888620000257701949 1218327333232500096638231)
                      ·
                        rfl

theorem cell23_2372684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2372684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372684 prefixEnd_2372684 := by exact prefixLift 2372684
  have htrace : WordTrace (prefixWord ++ tailWord_2372684) baseStart_2372684 baseEnd_2372684 := by
    simpa [prefixWord, tailWord_2372684, baseEnd_2372684] using wordTrace_append hprefix tailTrace_2372684
  have hstable : (prefixWord ++ tailWord_2372684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372684).length < 2 ^ (prefixWord ++ tailWord_2372684).sum := by decide
  have hdescent : baseEnd_2372684 < baseStart_2372684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372711 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_2372711 : Nat := 118140960795 + 2372711 * 2 ^ 59
def prefixEnd_2372711 : Nat := 4983230072969 + 3 ^ 40 * 2372711 * 2
def baseEnd_2372711 : Nat := 1218341197210171491000607

theorem tailTrace_2372711 : CollatzResearch.WordTrace tailWord_2372711 prefixEnd_2372711 1218341197210171491000607 := by
  unfold tailWord_2372711
  simp only [CollatzResearch.WordTrace]
  refine ⟨86539879707080748622157987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57693253138053832414771991 86539879707080748622157987)
  ·
    refine ⟨129809819560621122933236981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86539879707080748622157987 129809819560621122933236981)
    ·
      refine ⟨12169670583808230274990967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129809819560621122933236981 12169670583808230274990967)
      ·
        refine ⟨18254505875712345412486451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169670583808230274990967 18254505875712345412486451)
        ·
          refine ⟨27381758813568518118729677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254505875712345412486451 27381758813568518118729677)
          ·
            refine ⟨10268159555088194294523629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27381758813568518118729677 10268159555088194294523629)
            ·
              refine ⟨3850559833158072860446361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10268159555088194294523629 3850559833158072860446361)
              ·
                refine ⟨2887919874868554645334771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850559833158072860446361 2887919874868554645334771)
                ·
                  refine ⟨4331879812302831968002157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887919874868554645334771 4331879812302831968002157)
                  ·
                    refine ⟨1624454929613561988000809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4331879812302831968002157 1624454929613561988000809)
                    ·
                      refine ⟨1218341197210171491000607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624454929613561988000809 1218341197210171491000607)
                      ·
                        rfl

theorem cell23_2372711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_2372711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372711 prefixEnd_2372711 := by exact prefixLift 2372711
  have htrace : WordTrace (prefixWord ++ tailWord_2372711) baseStart_2372711 baseEnd_2372711 := by
    simpa [prefixWord, tailWord_2372711, baseEnd_2372711] using wordTrace_append hprefix tailTrace_2372711
  have hstable : (prefixWord ++ tailWord_2372711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372711).length < 2 ^ (prefixWord ++ tailWord_2372711).sum := by decide
  have hdescent : baseEnd_2372711 < baseStart_2372711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372754 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2372754 : Nat := 118140960795 + 2372754 * 2 ^ 59
def prefixEnd_2372754 : Nat := 4983230072969 + 3 ^ 40 * 2372754 * 2
def baseEnd_2372754 : Nat := 1218363276878314822762909

theorem tailTrace_2372754 : CollatzResearch.WordTrace tailWord_2372754 prefixEnd_2372754 1218363276878314822762909 := by
  unfold tailWord_2372754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21635362011481241741493329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57694298697283311310648877 21635362011481241741493329)
  ·
    refine ⟨16226521508610931306119997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21635362011481241741493329 16226521508610931306119997)
    ·
      refine ⟨6084945565729099239794999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16226521508610931306119997 6084945565729099239794999)
      ·
        refine ⟨9127418348593648859692499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6084945565729099239794999 9127418348593648859692499)
        ·
          refine ⟨13691127522890473289538749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9127418348593648859692499 13691127522890473289538749)
          ·
            refine ⟨5134172821083927483577031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13691127522890473289538749 5134172821083927483577031)
            ·
              refine ⟨7701259231625891225365547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134172821083927483577031 7701259231625891225365547)
              ·
                refine ⟨11551888847438836838048321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7701259231625891225365547 11551888847438836838048321)
                ·
                  refine ⟨8663916635579127628536241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11551888847438836838048321 8663916635579127628536241)
                  ·
                    refine ⟨6497937476684345721402181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8663916635579127628536241 6497937476684345721402181)
                    ·
                      refine ⟨1218363276878314822762909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6497937476684345721402181 1218363276878314822762909)
                      ·
                        rfl

theorem cell23_2372754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2372754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372754 prefixEnd_2372754 := by exact prefixLift 2372754
  have htrace : WordTrace (prefixWord ++ tailWord_2372754) baseStart_2372754 baseEnd_2372754 := by
    simpa [prefixWord, tailWord_2372754, baseEnd_2372754] using wordTrace_append hprefix tailTrace_2372754
  have hstable : (prefixWord ++ tailWord_2372754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372754).length < 2 ^ (prefixWord ++ tailWord_2372754).sum := by decide
  have hdescent : baseEnd_2372754 < baseStart_2372754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372854 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2372854 : Nat := 118140960795 + 2372854 * 2 ^ 59
def prefixEnd_2372854 : Nat := 4983230072969 + 3 ^ 40 * 2372854 * 2
def baseEnd_2372854 : Nat := 135379402771529381279161

theorem tailTrace_2372854 : CollatzResearch.WordTrace tailWord_2372854 prefixEnd_2372854 135379402771529381279161 := by
  unfold tailWord_2372854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409068459097667752788351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57696730230375122696409077 5409068459097667752788351)
  ·
    refine ⟨8113602688646501629182527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409068459097667752788351 8113602688646501629182527)
    ·
      refine ⟨12170404032969752443773791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8113602688646501629182527 12170404032969752443773791)
      ·
        refine ⟨18255606049454628665660687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12170404032969752443773791 18255606049454628665660687)
        ·
          refine ⟨27383409074181942998491031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18255606049454628665660687 27383409074181942998491031)
          ·
            refine ⟨41075113611272914497736547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27383409074181942998491031 41075113611272914497736547)
            ·
              refine ⟨61612670416909371746604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41075113611272914497736547 61612670416909371746604821)
              ·
                refine ⟨2888093925792626800622101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61612670416909371746604821 2888093925792626800622101)
                ·
                  refine ⟨135379402771529381279161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2888093925792626800622101 135379402771529381279161)
                  ·
                    rfl

theorem cell23_2372854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2372854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372854 prefixEnd_2372854 := by exact prefixLift 2372854
  have htrace : WordTrace (prefixWord ++ tailWord_2372854) baseStart_2372854 baseEnd_2372854 := by
    simpa [prefixWord, tailWord_2372854, baseEnd_2372854] using wordTrace_append hprefix tailTrace_2372854
  have hstable : (prefixWord ++ tailWord_2372854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372854).length < 2 ^ (prefixWord ++ tailWord_2372854).sum := by decide
  have hdescent : baseEnd_2372854 < baseStart_2372854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372858 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_2372858 : Nat := 118140960795 + 2372858 * 2 ^ 59
def prefixEnd_2372858 : Nat := 4983230072969 + 3 ^ 40 * 2372858 * 2
def baseEnd_2372858 : Nat := 406138892955460805287477

theorem tailTrace_2372858 : CollatzResearch.WordTrace tailWord_2372858 prefixEnd_2372858 406138892955460805287477 := by
  unfold tailWord_2372858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21636310309387048181939807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57696827491698795151839485 21636310309387048181939807)
  ·
    refine ⟨32454465464080572272909711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21636310309387048181939807 32454465464080572272909711)
    ·
      refine ⟨48681698196120858409364567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32454465464080572272909711 48681698196120858409364567)
      ·
        refine ⟨73022547294181287614046851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48681698196120858409364567 73022547294181287614046851)
        ·
          refine ⟨109533820941271931421070277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73022547294181287614046851 109533820941271931421070277)
          ·
            refine ⟨20537591426488487141450677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109533820941271931421070277 20537591426488487141450677)
            ·
              refine ⟨1925399196233295669511001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20537591426488487141450677 1925399196233295669511001)
              ·
                refine ⟨1444049397174971752133251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925399196233295669511001 1444049397174971752133251)
                ·
                  refine ⟨2166074095762457628199877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444049397174971752133251 2166074095762457628199877)
                  ·
                    refine ⟨406138892955460805287477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166074095762457628199877 406138892955460805287477)
                    ·
                      rfl

theorem cell23_2372858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_2372858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372858 prefixEnd_2372858 := by exact prefixLift 2372858
  have htrace : WordTrace (prefixWord ++ tailWord_2372858) baseStart_2372858 baseEnd_2372858 := by
    simpa [prefixWord, tailWord_2372858, baseEnd_2372858] using wordTrace_append hprefix tailTrace_2372858
  have hstable : (prefixWord ++ tailWord_2372858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372858).length < 2 ^ (prefixWord ++ tailWord_2372858).sum := by decide
  have hdescent : baseEnd_2372858 < baseStart_2372858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372907 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_2372907 : Nat := 118140960795 + 2372907 * 2 ^ 59
def prefixEnd_2372907 : Nat := 4983230072969 + 3 ^ 40 * 2372907 * 2
def baseEnd_2372907 : Nat := 1218441839418452724149705

theorem tailTrace_2372907 : CollatzResearch.WordTrace tailWord_2372907 prefixEnd_2372907 1218441839418452724149705 := by
  unfold tailWord_2372907
  simp only [CollatzResearch.WordTrace]
  refine ⟨86547028414370674096292975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57698018942913782730861983 86547028414370674096292975)
  ·
    refine ⟨129820542621556011144439463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86547028414370674096292975 129820542621556011144439463)
    ·
      refine ⟨194730813932334016716659195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129820542621556011144439463 194730813932334016716659195)
      ·
        refine ⟨292096220898501025074988793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194730813932334016716659195 292096220898501025074988793)
        ·
          refine ⟨219072165673875768806241595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292096220898501025074988793 219072165673875768806241595)
          ·
            refine ⟨328608248510813653209362393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219072165673875768806241595 328608248510813653209362393)
            ·
              refine ⟨246456186383110239907021795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328608248510813653209362393 246456186383110239907021795)
              ·
                refine ⟨369684279574665359860532693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246456186383110239907021795 369684279574665359860532693)
                ·
                  refine ⟨8664475302531219371731235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 369684279574665359860532693 8664475302531219371731235)
                  ·
                    refine ⟨12996712953796829057596853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8664475302531219371731235 12996712953796829057596853)
                    ·
                      refine ⟨1218441839418452724149705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12996712953796829057596853 1218441839418452724149705)
                      ·
                        rfl

theorem cell23_2372907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_2372907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372907 prefixEnd_2372907 := by exact prefixLift 2372907
  have htrace : WordTrace (prefixWord ++ tailWord_2372907) baseStart_2372907 baseEnd_2372907 := by
    simpa [prefixWord, tailWord_2372907, baseEnd_2372907] using wordTrace_append hprefix tailTrace_2372907
  have hstable : (prefixWord ++ tailWord_2372907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372907).length < 2 ^ (prefixWord ++ tailWord_2372907).sum := by decide
  have hdescent : baseEnd_2372907 < baseStart_2372907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372915 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 1, 1, 3]
def baseStart_2372915 : Nat := 118140960795 + 2372915 * 2 ^ 59
def prefixEnd_2372915 : Nat := 4983230072969 + 3 ^ 40 * 2372915 * 2
def baseEnd_2372915 : Nat := 1218445947263688692849669

theorem tailTrace_2372915 : CollatzResearch.WordTrace tailWord_2372915 prefixEnd_2372915 1218445947263688692849669 := by
  unfold tailWord_2372915
  simp only [CollatzResearch.WordTrace]
  refine ⟨86547320198341691462584199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57698213465561127641722799 86547320198341691462584199)
  ·
    refine ⟨129820980297512537193876299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86547320198341691462584199 129820980297512537193876299)
    ·
      refine ⟨194731470446268805790814449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129820980297512537193876299 194731470446268805790814449)
      ·
        refine ⟨146048602834701604343110837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194731470446268805790814449 146048602834701604343110837)
        ·
          refine ⟨13692056515753275407166641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146048602834701604343110837 13692056515753275407166641)
          ·
            refine ⟨10269042386814956555374981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13692056515753275407166641 10269042386814956555374981)
            ·
              refine ⟨1925445447527804354132809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10269042386814956555374981 1925445447527804354132809)
              ·
                refine ⟨1444084085645853265599607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925445447527804354132809 1444084085645853265599607)
                ·
                  refine ⟨2166126128468779898399411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444084085645853265599607 2166126128468779898399411)
                  ·
                    refine ⟨3249189192703169847599117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166126128468779898399411 3249189192703169847599117)
                    ·
                      refine ⟨1218445947263688692849669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3249189192703169847599117 1218445947263688692849669)
                      ·
                        rfl

theorem cell23_2372915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 1, 3].length) (baseStart_2372915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372915 prefixEnd_2372915 := by exact prefixLift 2372915
  have htrace : WordTrace (prefixWord ++ tailWord_2372915) baseStart_2372915 baseEnd_2372915 := by
    simpa [prefixWord, tailWord_2372915, baseEnd_2372915] using wordTrace_append hprefix tailTrace_2372915
  have hstable : (prefixWord ++ tailWord_2372915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372915).length < 2 ^ (prefixWord ++ tailWord_2372915).sum := by decide
  have hdescent : baseEnd_2372915 < baseStart_2372915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372944 : List Nat := [2, 1, 1, 1, 1, 5, 5, 7]
def baseStart_2372944 : Nat := 118140960795 + 2372944 * 2 ^ 59
def prefixEnd_2372944 : Nat := 4983230072969 + 3 ^ 40 * 2372944 * 2
def baseEnd_2372944 : Nat := 45128179192691447384705

theorem tailTrace_2372944 : CollatzResearch.WordTrace tailWord_2372944 prefixEnd_2372944 45128179192691447384705 := by
  unfold tailWord_2372944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43274188957618314707694943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57698918610157752943593257 43274188957618314707694943)
  ·
    refine ⟨64911283436427472061542415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43274188957618314707694943 64911283436427472061542415)
    ·
      refine ⟨97366925154641208092313623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64911283436427472061542415 97366925154641208092313623)
      ·
        refine ⟨146050387731961812138470435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97366925154641208092313623 146050387731961812138470435)
        ·
          refine ⟨219075581597942718207705653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146050387731961812138470435 219075581597942718207705653)
          ·
            refine ⟨20538335774807129831972405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219075581597942718207705653 20538335774807129831972405)
            ·
              refine ⟨1925468978888168421747413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20538335774807129831972405 1925468978888168421747413)
              ·
                refine ⟨45128179192691447384705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1925468978888168421747413 45128179192691447384705)
                ·
                  rfl

theorem cell23_2372944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 7].length) (baseStart_2372944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2372944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2372944 prefixEnd_2372944 := by exact prefixLift 2372944
  have htrace : WordTrace (prefixWord ++ tailWord_2372944) baseStart_2372944 baseEnd_2372944 := by
    simpa [prefixWord, tailWord_2372944, baseEnd_2372944] using wordTrace_append hprefix tailTrace_2372944
  have hstable : (prefixWord ++ tailWord_2372944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372944).length < 2 ^ (prefixWord ++ tailWord_2372944).sum := by decide
  have hdescent : baseEnd_2372944 < baseStart_2372944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373006 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2373006 : Nat := 118140960795 + 2373006 * 2 ^ 59
def prefixEnd_2373006 : Nat := 4983230072969 + 3 ^ 40 * 2373006 * 2
def baseEnd_2373006 : Nat := 1218492674003247836811751

theorem tailTrace_2373006 : CollatzResearch.WordTrace tailWord_2373006 prefixEnd_2373006 1218492674003247836811751 := by
  unfold tailWord_2373006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10818829905126501750518359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57700426160674676002764581 10818829905126501750518359)
  ·
    refine ⟨16228244857689752625777539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10818829905126501750518359 16228244857689752625777539)
    ·
      refine ⟨24342367286534628938666309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16228244857689752625777539 24342367286534628938666309)
      ·
        refine ⟨4564193866225242925999933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24342367286534628938666309 4564193866225242925999933)
        ·
          refine ⟨1711572699834466097249975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4564193866225242925999933 1711572699834466097249975)
          ·
            refine ⟨2567359049751699145874963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711572699834466097249975 2567359049751699145874963)
            ·
              refine ⟨3851038574627548718812445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567359049751699145874963 3851038574627548718812445)
              ·
                refine ⟨1444139465485330769554667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3851038574627548718812445 1444139465485330769554667)
                ·
                  refine ⟨2166209198227996154332001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444139465485330769554667 2166209198227996154332001)
                  ·
                    refine ⟨1624656898670997115749001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166209198227996154332001 1624656898670997115749001)
                    ·
                      refine ⟨1218492674003247836811751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624656898670997115749001 1218492674003247836811751)
                      ·
                        rfl

theorem cell23_2373006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2373006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373006 prefixEnd_2373006 := by exact prefixLift 2373006
  have htrace : WordTrace (prefixWord ++ tailWord_2373006) baseStart_2373006 baseEnd_2373006 := by
    simpa [prefixWord, tailWord_2373006, baseEnd_2373006] using wordTrace_append hprefix tailTrace_2373006
  have hstable : (prefixWord ++ tailWord_2373006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373006).length < 2 ^ (prefixWord ++ tailWord_2373006).sum := by decide
  have hdescent : baseEnd_2373006 < baseStart_2373006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373031 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2373031 : Nat := 118140960795 + 2373031 * 2 ^ 59
def prefixEnd_2373031 : Nat := 4983230072969 + 3 ^ 40 * 2373031 * 2
def baseEnd_2373031 : Nat := 1218505511019610238999135

theorem tailTrace_2373031 : CollatzResearch.WordTrace tailWord_2373031 prefixEnd_2373031 1218505511019610238999135 := by
  unfold tailWord_2373031
  simp only [CollatzResearch.WordTrace]
  refine ⟨86551551065921443273806947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57701034043947628849204631 86551551065921443273806947)
  ·
    refine ⟨129827326598882164910710421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86551551065921443273806947 129827326598882164910710421)
    ·
      refine ⟨6085655934322601480189551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129827326598882164910710421 6085655934322601480189551)
      ·
        refine ⟨9128483901483902220284327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085655934322601480189551 9128483901483902220284327)
        ·
          refine ⟨13692725852225853330426491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9128483901483902220284327 13692725852225853330426491)
          ·
            refine ⟨20539088778338779995639737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13692725852225853330426491 20539088778338779995639737)
            ·
              refine ⟨15404316583754084996729803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20539088778338779995639737 15404316583754084996729803)
              ·
                refine ⟨23106474875631127495094705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15404316583754084996729803 23106474875631127495094705)
                ·
                  refine ⟨17329856156723345621321029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23106474875631127495094705 17329856156723345621321029)
                  ·
                    refine ⟨3249348029385627303997693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17329856156723345621321029 3249348029385627303997693)
                    ·
                      refine ⟨1218505511019610238999135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3249348029385627303997693 1218505511019610238999135)
                      ·
                        rfl

theorem cell23_2373031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2373031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373031 prefixEnd_2373031 := by exact prefixLift 2373031
  have htrace : WordTrace (prefixWord ++ tailWord_2373031) baseStart_2373031 baseEnd_2373031 := by
    simpa [prefixWord, tailWord_2373031, baseEnd_2373031] using wordTrace_append hprefix tailTrace_2373031
  have hstable : (prefixWord ++ tailWord_2373031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373031).length < 2 ^ (prefixWord ++ tailWord_2373031).sum := by decide
  have hdescent : baseEnd_2373031 < baseStart_2373031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373081 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_2373081 : Nat := 118140960795 + 2373081 * 2 ^ 59
def prefixEnd_2373081 : Nat := 4983230072969 + 3 ^ 40 * 2373081 * 2
def baseEnd_2373081 : Nat := 406177061684111681124635

theorem tailTrace_2373081 : CollatzResearch.WordTrace tailWord_2373081 prefixEnd_2373081 406177061684111681124635 := by
  unfold tailWord_2373081
  simp only [CollatzResearch.WordTrace]
  refine ⟨86553374715740301813127097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57702249810493534542084731 86553374715740301813127097)
  ·
    refine ⟨64915031036805226359845323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86553374715740301813127097 64915031036805226359845323)
    ·
      refine ⟨97372546555207839539767985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64915031036805226359845323 97372546555207839539767985)
      ·
        refine ⟨73029409916405879654825989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97372546555207839539767985 73029409916405879654825989)
        ·
          refine ⟨13693014359326102435279873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73029409916405879654825989 13693014359326102435279873)
          ·
            refine ⟨10269760769494576826459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13693014359326102435279873 10269760769494576826459905)
            ·
              refine ⟨7702320577120932619844929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10269760769494576826459905 7702320577120932619844929)
              ·
                refine ⟨5776740432840699464883697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702320577120932619844929 5776740432840699464883697)
                ·
                  refine ⟨4332555324630524598662773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5776740432840699464883697 4332555324630524598662773)
                  ·
                    refine ⟨406177061684111681124635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4332555324630524598662773 406177061684111681124635)
                    ·
                      rfl

theorem cell23_2373081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_2373081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373081 prefixEnd_2373081 := by exact prefixLift 2373081
  have htrace : WordTrace (prefixWord ++ tailWord_2373081) baseStart_2373081 baseEnd_2373081 := by
    simpa [prefixWord, tailWord_2373081, baseEnd_2373081] using wordTrace_append hprefix tailTrace_2373081
  have hstable : (prefixWord ++ tailWord_2373081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373081).length < 2 ^ (prefixWord ++ tailWord_2373081).sum := by decide
  have hdescent : baseEnd_2373081 < baseStart_2373081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373085 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 5]
def baseStart_2373085 : Nat := 118140960795 + 2373085 * 2 ^ 59
def prefixEnd_2373085 : Nat := 4983230072969 + 3 ^ 40 * 2373085 * 2
def baseEnd_2373085 : Nat := 135392582108328114191543

theorem tailTrace_2373085 : CollatzResearch.WordTrace tailWord_2373085 prefixEnd_2373085 135392582108328114191543 := by
  unfold tailWord_2373085
  simp only [CollatzResearch.WordTrace]
  refine ⟨86553520607725810496272709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57702347071817206997515139 86553520607725810496272709)
  ·
    refine ⟨16228785113948589468051133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86553520607725810496272709 16228785113948589468051133)
    ·
      refine ⟨6085794417730721050519175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16228785113948589468051133 6085794417730721050519175)
      ·
        refine ⟨9128691626596081575778763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085794417730721050519175 9128691626596081575778763)
        ·
          refine ⟨13693037439894122363668145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9128691626596081575778763 13693037439894122363668145)
          ·
            refine ⟨10269778079920591772751109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13693037439894122363668145 10269778079920591772751109)
            ·
              refine ⟨1925583389985110957390833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10269778079920591772751109 1925583389985110957390833)
              ·
                refine ⟨1444187542488833218043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925583389985110957390833 1444187542488833218043125)
                ·
                  refine ⟨135392582108328114191543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1444187542488833218043125 135392582108328114191543)
                  ·
                    rfl

theorem cell23_2373085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_2373085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373085 prefixEnd_2373085 := by exact prefixLift 2373085
  have htrace : WordTrace (prefixWord ++ tailWord_2373085) baseStart_2373085 baseEnd_2373085 := by
    simpa [prefixWord, tailWord_2373085, baseEnd_2373085] using wordTrace_append hprefix tailTrace_2373085
  have hstable : (prefixWord ++ tailWord_2373085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373085).length < 2 ^ (prefixWord ++ tailWord_2373085).sum := by decide
  have hdescent : baseEnd_2373085 < baseStart_2373085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373091 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2373091 : Nat := 118140960795 + 2373091 * 2 ^ 59
def prefixEnd_2373091 : Nat := 4983230072969 + 3 ^ 40 * 2373091 * 2
def baseEnd_2373091 : Nat := 1218536319858880004248859

theorem tailTrace_2373091 : CollatzResearch.WordTrace tailWord_2373091 prefixEnd_2373091 1218536319858880004248859 := by
  unfold tailWord_2373091
  simp only [CollatzResearch.WordTrace]
  refine ⟨86553739445704073520991127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57702492963802715680660751 86553739445704073520991127)
  ·
    refine ⟨129830609168556110281486691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86553739445704073520991127 129830609168556110281486691)
    ·
      refine ⟨194745913752834165422230037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129830609168556110281486691 194745913752834165422230037)
      ·
        refine ⟨9128714707164101504167033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194745913752834165422230037 9128714707164101504167033)
        ·
          refine ⟨6846536030373076128125275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9128714707164101504167033 6846536030373076128125275)
          ·
            refine ⟨10269804045559614192187913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846536030373076128125275 10269804045559614192187913)
            ·
              refine ⟨7702353034169710644140935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10269804045559614192187913 7702353034169710644140935)
              ·
                refine ⟨11553529551254565966211403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7702353034169710644140935 11553529551254565966211403)
                ·
                  refine ⟨17330294326881848949317105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11553529551254565966211403 17330294326881848949317105)
                  ·
                    refine ⟨12997720745161386711987829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17330294326881848949317105 12997720745161386711987829)
                    ·
                      refine ⟨1218536319858880004248859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12997720745161386711987829 1218536319858880004248859)
                      ·
                        rfl

theorem cell23_2373091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2373091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373091 prefixEnd_2373091 := by exact prefixLift 2373091
  have htrace : WordTrace (prefixWord ++ tailWord_2373091) baseStart_2373091 baseEnd_2373091 := by
    simpa [prefixWord, tailWord_2373091, baseEnd_2373091] using wordTrace_append hprefix tailTrace_2373091
  have hstable : (prefixWord ++ tailWord_2373091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373091).length < 2 ^ (prefixWord ++ tailWord_2373091).sum := by decide
  have hdescent : baseEnd_2373091 < baseStart_2373091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373141 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 8]
def baseStart_2373141 : Nat := 118140960795 + 2373141 * 2 ^ 59
def prefixEnd_2373141 : Nat := 4983230072969 + 3 ^ 40 * 2373141 * 2
def baseEnd_2373141 : Nat := 135395777099067200958181

theorem tailTrace_2373141 : CollatzResearch.WordTrace tailWord_2373141 prefixEnd_2373141 135395777099067200958181 := by
  unfold tailWord_2373141
  simp only [CollatzResearch.WordTrace]
  refine ⟨86555563095522932060311277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57703708730348621373540851 86555563095522932060311277)
  ·
    refine ⟨32458336160821099522616729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86555563095522932060311277 32458336160821099522616729)
    ·
      refine ⟨24343752120615824641962547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32458336160821099522616729 24343752120615824641962547)
      ·
        refine ⟨36515628180923736962943821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24343752120615824641962547 36515628180923736962943821)
        ·
          refine ⟨13693360567846401361103933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36515628180923736962943821 13693360567846401361103933)
          ·
            refine ⟨5135010212942400510413975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13693360567846401361103933 5135010212942400510413975)
            ·
              refine ⟨7702515319413600765620963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135010212942400510413975 7702515319413600765620963)
              ·
                refine ⟨11553772979120401148431445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7702515319413600765620963 11553772979120401148431445)
                ·
                  refine ⟨135395777099067200958181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11553772979120401148431445 135395777099067200958181)
                  ·
                    rfl

theorem cell23_2373141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_2373141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373141 prefixEnd_2373141 := by exact prefixLift 2373141
  have htrace : WordTrace (prefixWord ++ tailWord_2373141) baseStart_2373141 baseEnd_2373141 := by
    simpa [prefixWord, tailWord_2373141, baseEnd_2373141] using wordTrace_append hprefix tailTrace_2373141
  have hstable : (prefixWord ++ tailWord_2373141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373141).length < 2 ^ (prefixWord ++ tailWord_2373141).sum := by decide
  have hdescent : baseEnd_2373141 < baseStart_2373141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373178 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_2373178 : Nat := 118140960795 + 2373178 * 2 ^ 59
def prefixEnd_2373178 : Nat := 4983230072969 + 3 ^ 40 * 2373178 * 2
def baseEnd_2373178 : Nat := 1218580992675821163860959

theorem tailTrace_2373178 : CollatzResearch.WordTrace tailWord_2373178 prefixEnd_2373178 1218580992675821163860959 := by
  unfold tailWord_2373178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639228149097221844852047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57704608397592591586272125 21639228149097221844852047)
  ·
    refine ⟨32458842223645832767278071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21639228149097221844852047 32458842223645832767278071)
    ·
      refine ⟨48688263335468749150917107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32458842223645832767278071 48688263335468749150917107)
      ·
        refine ⟨73032395003203123726375661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48688263335468749150917107 73032395003203123726375661)
        ·
          refine ⟨27387148126201171397390873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73032395003203123726375661 27387148126201171397390873)
          ·
            refine ⟨20540361094650878548043155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27387148126201171397390873 20540361094650878548043155)
            ·
              refine ⟨30810541641976317822064733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20540361094650878548043155 30810541641976317822064733)
              ·
                refine ⟨11553953115741119183274275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30810541641976317822064733 11553953115741119183274275)
                ·
                  refine ⟨17330929673611678774911413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11553953115741119183274275 17330929673611678774911413)
                  ·
                    refine ⟨1624774656901094885147945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17330929673611678774911413 1624774656901094885147945)
                    ·
                      refine ⟨1218580992675821163860959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624774656901094885147945 1218580992675821163860959)
                      ·
                        rfl

theorem cell23_2373178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_2373178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373178 prefixEnd_2373178 := by exact prefixLift 2373178
  have htrace : WordTrace (prefixWord ++ tailWord_2373178) baseStart_2373178 baseEnd_2373178 := by
    simpa [prefixWord, tailWord_2373178, baseEnd_2373178] using wordTrace_append hprefix tailTrace_2373178
  have hstable : (prefixWord ++ tailWord_2373178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373178).length < 2 ^ (prefixWord ++ tailWord_2373178).sum := by decide
  have hdescent : baseEnd_2373178 < baseStart_2373178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373202 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2373202 : Nat := 118140960795 + 2373202 * 2 ^ 59
def prefixEnd_2373202 : Nat := 4983230072969 + 3 ^ 40 * 2373202 * 2
def baseEnd_2373202 : Nat := 1218593316211529069960849

theorem tailTrace_2373202 : CollatzResearch.WordTrace tailWord_2373202 prefixEnd_2373202 1218593316211529069960849 := by
  unfold tailWord_2373202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639446987075484869570465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57705191965534626318854573 21639446987075484869570465)
  ·
    refine ⟨16229585240306613652177849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21639446987075484869570465 16229585240306613652177849)
    ·
      refine ⟨12172188930229960239133387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16229585240306613652177849 12172188930229960239133387)
      ·
        refine ⟨18258283395344940358700081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12172188930229960239133387 18258283395344940358700081)
        ·
          refine ⟨13693712546508705269025061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18258283395344940358700081 13693712546508705269025061)
          ·
            refine ⟨2567571102470382237942199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13693712546508705269025061 2567571102470382237942199)
            ·
              refine ⟨3851356653705573356913299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567571102470382237942199 3851356653705573356913299)
              ·
                refine ⟨5777034980558360035369949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851356653705573356913299 5777034980558360035369949)
                ·
                  refine ⟨2166388117709385013263731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5777034980558360035369949 2166388117709385013263731)
                  ·
                    refine ⟨3249582176564077519895597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166388117709385013263731 3249582176564077519895597)
                    ·
                      refine ⟨1218593316211529069960849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3249582176564077519895597 1218593316211529069960849)
                      ·
                        rfl

theorem cell23_2373202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2373202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373202 prefixEnd_2373202 := by exact prefixLift 2373202
  have htrace : WordTrace (prefixWord ++ tailWord_2373202) baseStart_2373202 baseEnd_2373202 := by
    simpa [prefixWord, tailWord_2373202, baseEnd_2373202] using wordTrace_append hprefix tailTrace_2373202
  have hstable : (prefixWord ++ tailWord_2373202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373202).length < 2 ^ (prefixWord ++ tailWord_2373202).sum := by decide
  have hdescent : baseEnd_2373202 < baseStart_2373202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373225 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 3, 2, 2]
def baseStart_2373225 : Nat := 118140960795 + 2373225 * 2 ^ 59
def prefixEnd_2373225 : Nat := 4983230072969 + 3 ^ 40 * 2373225 * 2
def baseEnd_2373225 : Nat := 1218605126266582479973243

theorem tailTrace_2373225 : CollatzResearch.WordTrace tailWord_2373225 prefixEnd_2373225 1218605126266582479973243 := by
  unfold tailWord_2373225
  simp only [CollatzResearch.WordTrace]
  refine ⟨86558626827218614406369129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57705751218145742937579419 86558626827218614406369129)
  ·
    refine ⟨64918970120413960804776847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86558626827218614406369129 64918970120413960804776847)
    ·
      refine ⟨97378455180620941207165271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64918970120413960804776847 97378455180620941207165271)
      ·
        refine ⟨146067682770931411810747907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97378455180620941207165271 146067682770931411810747907)
        ·
          refine ⟨219101524156397117716121861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146067682770931411810747907 219101524156397117716121861)
          ·
            refine ⟨41081535779324459571772849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219101524156397117716121861 41081535779324459571772849)
            ·
              refine ⟨30811151834493344678829637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41081535779324459571772849 30811151834493344678829637)
              ·
                refine ⟨5777090968967502127280557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30811151834493344678829637 5777090968967502127280557)
                ·
                  refine ⟨2166409113362813297730209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5777090968967502127280557 2166409113362813297730209)
                  ·
                    refine ⟨1624806835022109973297657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166409113362813297730209 1624806835022109973297657)
                    ·
                      refine ⟨1218605126266582479973243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624806835022109973297657 1218605126266582479973243)
                      ·
                        rfl

theorem cell23_2373225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2, 2].length) (baseStart_2373225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373225 prefixEnd_2373225 := by exact prefixLift 2373225
  have htrace : WordTrace (prefixWord ++ tailWord_2373225) baseStart_2373225 baseEnd_2373225 := by
    simpa [prefixWord, tailWord_2373225, baseEnd_2373225] using wordTrace_append hprefix tailTrace_2373225
  have hstable : (prefixWord ++ tailWord_2373225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373225).length < 2 ^ (prefixWord ++ tailWord_2373225).sum := by decide
  have hdescent : baseEnd_2373225 < baseStart_2373225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373245 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_2373245 : Nat := 118140960795 + 2373245 * 2 ^ 59
def prefixEnd_2373245 : Nat := 4983230072969 + 3 ^ 40 * 2373245 * 2
def baseEnd_2373245 : Nat := 1218615395879672401723151

theorem tailTrace_2373245 : CollatzResearch.WordTrace tailWord_2373245 prefixEnd_2373245 1218615395879672401723151 := by
  unfold tailWord_2373245
  simp only [CollatzResearch.WordTrace]
  refine ⟨86559356287146157822097189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57706237524764105214731459 86559356287146157822097189)
  ·
    refine ⟨16229879303839904591643223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86559356287146157822097189 16229879303839904591643223)
    ·
      refine ⟨24344818955759856887464835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16229879303839904591643223 24344818955759856887464835)
      ·
        refine ⟨36517228433639785331197253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24344818955759856887464835 36517228433639785331197253)
        ·
          refine ⟨6846980331307459749599485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36517228433639785331197253 6846980331307459749599485)
          ·
            refine ⟨2567617624240297406099807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6846980331307459749599485 2567617624240297406099807)
            ·
              refine ⟨3851426436360446109149711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567617624240297406099807 3851426436360446109149711)
              ·
                refine ⟨5777139654540669163724567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851426436360446109149711 5777139654540669163724567)
                ·
                  refine ⟨8665709481811003745586851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777139654540669163724567 8665709481811003745586851)
                  ·
                    refine ⟨12998564222716505618380277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8665709481811003745586851 12998564222716505618380277)
                    ·
                      refine ⟨1218615395879672401723151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12998564222716505618380277 1218615395879672401723151)
                      ·
                        rfl

theorem cell23_2373245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_2373245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373245 prefixEnd_2373245 := by exact prefixLift 2373245
  have htrace : WordTrace (prefixWord ++ tailWord_2373245) baseStart_2373245 baseEnd_2373245 := by
    simpa [prefixWord, tailWord_2373245, baseEnd_2373245] using wordTrace_append hprefix tailTrace_2373245
  have hstable : (prefixWord ++ tailWord_2373245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373245).length < 2 ^ (prefixWord ++ tailWord_2373245).sum := by decide
  have hdescent : baseEnd_2373245 < baseStart_2373245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373252 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_2373252 : Nat := 118140960795 + 2373252 * 2 ^ 59
def prefixEnd_2373252 : Nat := 4983230072969 + 3 ^ 40 * 2373252 * 2
def baseEnd_2373252 : Nat := 406206330081417958111873

theorem tailTrace_2373252 : CollatzResearch.WordTrace tailWord_2373252 prefixEnd_2373252 406206330081417958111873 := by
  unfold tailWord_2373252
  simp only [CollatzResearch.WordTrace]
  refine ⟨43279805799060399008801005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57706407732080532011734673 43279805799060399008801005)
  ·
    refine ⟨16229927174647649628300377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43279805799060399008801005 16229927174647649628300377)
    ·
      refine ⟨12172445380985737221225283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16229927174647649628300377 12172445380985737221225283)
      ·
        refine ⟨18258668071478605831837925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12172445380985737221225283 18258668071478605831837925)
        ·
          refine ⟨3423500263402238593469611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18258668071478605831837925 3423500263402238593469611)
          ·
            refine ⟨5135250395103357890204417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423500263402238593469611 5135250395103357890204417)
            ·
              refine ⟨3851437796327518417653313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5135250395103357890204417 3851437796327518417653313)
              ·
                refine ⟨2888578347245638813239985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851437796327518417653313 2888578347245638813239985)
                ·
                  refine ⟨2166433760434229109929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2888578347245638813239985 2166433760434229109929989)
                  ·
                    refine ⟨406206330081417958111873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166433760434229109929989 406206330081417958111873)
                    ·
                      rfl

theorem cell23_2373252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_2373252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373252 prefixEnd_2373252 := by exact prefixLift 2373252
  have htrace : WordTrace (prefixWord ++ tailWord_2373252) baseStart_2373252 baseEnd_2373252 := by
    simpa [prefixWord, tailWord_2373252, baseEnd_2373252] using wordTrace_append hprefix tailTrace_2373252
  have hstable : (prefixWord ++ tailWord_2373252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373252).length < 2 ^ (prefixWord ++ tailWord_2373252).sum := by decide
  have hdescent : baseEnd_2373252 < baseStart_2373252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373282 : List Nat := [3, 3, 1, 4, 1, 1, 3, 7]
def baseStart_2373282 : Nat := 118140960795 + 2373282 * 2 ^ 59
def prefixEnd_2373282 : Nat := 4983230072969 + 3 ^ 40 * 2373282 * 2
def baseEnd_2373282 : Nat := 45134607209773657665203

theorem tailTrace_2373282 : CollatzResearch.WordTrace tailWord_2373282 prefixEnd_2373282 45134607209773657665203 := by
  unfold tailWord_2373282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640176447003028285298525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57707137192008075427462733 21640176447003028285298525)
  ·
    refine ⟨8115066167626135606986947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21640176447003028285298525 8115066167626135606986947)
    ·
      refine ⟨12172599251439203410480421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8115066167626135606986947 12172599251439203410480421)
      ·
        refine ⟨2282362359644850639465079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12172599251439203410480421 2282362359644850639465079)
        ·
          refine ⟨3423543539467275959197619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282362359644850639465079 3423543539467275959197619)
          ·
            refine ⟨5135315309200913938796429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423543539467275959197619 5135315309200913938796429)
            ·
              refine ⟨1925743240950342727048661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5135315309200913938796429 1925743240950342727048661)
              ·
                refine ⟨45134607209773657665203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1925743240950342727048661 45134607209773657665203)
                ·
                  rfl

theorem cell23_2373282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_2373282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373282 prefixEnd_2373282 := by exact prefixLift 2373282
  have htrace : WordTrace (prefixWord ++ tailWord_2373282) baseStart_2373282 baseEnd_2373282 := by
    simpa [prefixWord, tailWord_2373282, baseEnd_2373282] using wordTrace_append hprefix tailTrace_2373282
  have hstable : (prefixWord ++ tailWord_2373282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373282).length < 2 ^ (prefixWord ++ tailWord_2373282).sum := by decide
  have hdescent : baseEnd_2373282 < baseStart_2373282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373285 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_2373285 : Nat := 118140960795 + 2373285 * 2 ^ 59
def prefixEnd_2373285 : Nat := 4983230072969 + 3 ^ 40 * 2373285 * 2
def baseEnd_2373285 : Nat := 1218635935105852245222967

theorem tailTrace_2373285 : CollatzResearch.WordTrace tailWord_2373285 prefixEnd_2373285 1218635935105852245222967 := by
  unfold tailWord_2373285
  simp only [CollatzResearch.WordTrace]
  refine ⟨86560815207001244653553309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57707210138000829769035539 86560815207001244653553309)
  ·
    refine ⟨32460305702625466745082491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86560815207001244653553309 32460305702625466745082491)
    ·
      refine ⟨48690458553938200117623737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32460305702625466745082491 48690458553938200117623737)
      ·
        refine ⟨36517843915453650088217803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48690458553938200117623737 36517843915453650088217803)
        ·
          refine ⟨54776765873180475132326705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36517843915453650088217803 54776765873180475132326705)
          ·
            refine ⟨41082574404885356349245029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54776765873180475132326705 41082574404885356349245029)
            ·
              refine ⟨7702982700916004315483443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41082574404885356349245029 7702982700916004315483443)
              ·
                refine ⟨11554474051374006473225165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7702982700916004315483443 11554474051374006473225165)
                ·
                  refine ⟨4332927769265252427459437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11554474051374006473225165 4332927769265252427459437)
                  ·
                    refine ⟨1624847913474469660297289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4332927769265252427459437 1624847913474469660297289)
                    ·
                      refine ⟨1218635935105852245222967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624847913474469660297289 1218635935105852245222967)
                      ·
                        rfl

theorem cell23_2373285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_2373285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373285 prefixEnd_2373285 := by exact prefixLift 2373285
  have htrace : WordTrace (prefixWord ++ tailWord_2373285) baseStart_2373285 baseEnd_2373285 := by
    simpa [prefixWord, tailWord_2373285, baseEnd_2373285] using wordTrace_append hprefix tailTrace_2373285
  have hstable : (prefixWord ++ tailWord_2373285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373285).length < 2 ^ (prefixWord ++ tailWord_2373285).sum := by decide
  have hdescent : baseEnd_2373285 < baseStart_2373285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373308 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2373308 : Nat := 118140960795 + 2373308 * 2 ^ 59
def prefixEnd_2373308 : Nat := 4983230072969 + 3 ^ 40 * 2373308 * 2
def baseEnd_2373308 : Nat := 406215915053635218411787

theorem tailTrace_2373308 : CollatzResearch.WordTrace tailWord_2373308 prefixEnd_2373308 406215915053635218411787 := by
  unfold tailWord_2373308
  simp only [CollatzResearch.WordTrace]
  refine ⟨43280827042958959790820289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57707769390611946387760385 43280827042958959790820289)
  ·
    refine ⟨32460620282219219843115217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43280827042958959790820289 32460620282219219843115217)
    ·
      refine ⟨24345465211664414882336413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32460620282219219843115217 24345465211664414882336413)
      ·
        refine ⟨9129549454374155580876155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24345465211664414882336413 9129549454374155580876155)
        ·
          refine ⟨13694324181561233371314233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9129549454374155580876155 13694324181561233371314233)
          ·
            refine ⟨10270743136170925028485675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13694324181561233371314233 10270743136170925028485675)
            ·
              refine ⟨15406114704256387542728513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10270743136170925028485675 15406114704256387542728513)
              ·
                refine ⟨11554586028192290657046385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15406114704256387542728513 11554586028192290657046385)
                ·
                  refine ⟨8665939521144217992784789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11554586028192290657046385 8665939521144217992784789)
                  ·
                    refine ⟨406215915053635218411787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8665939521144217992784789 406215915053635218411787)
                    ·
                      rfl

theorem cell23_2373308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2373308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373308 prefixEnd_2373308 := by exact prefixLift 2373308
  have htrace : WordTrace (prefixWord ++ tailWord_2373308) baseStart_2373308 baseEnd_2373308 := by
    simpa [prefixWord, tailWord_2373308, baseEnd_2373308] using wordTrace_append hprefix tailTrace_2373308
  have hstable : (prefixWord ++ tailWord_2373308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373308).length < 2 ^ (prefixWord ++ tailWord_2373308).sum := by decide
  have hdescent : baseEnd_2373308 < baseStart_2373308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373338 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_2373338 : Nat := 118140960795 + 2373338 * 2 ^ 59
def prefixEnd_2373338 : Nat := 4983230072969 + 3 ^ 40 * 2373338 * 2
def baseEnd_2373338 : Nat := 135407016620060059762247

theorem tailTrace_2373338 : CollatzResearch.WordTrace tailWord_2373338 prefixEnd_2373338 135407016620060059762247 := by
  unfold tailWord_2373338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640687068952308676308167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57708498850539489803488445 21640687068952308676308167)
  ·
    refine ⟨32461030603428463014462251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21640687068952308676308167 32461030603428463014462251)
    ·
      refine ⟨48691545905142694521693377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32461030603428463014462251 48691545905142694521693377)
      ·
        refine ⟨36518659428857020891270033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48691545905142694521693377 36518659428857020891270033)
        ·
          refine ⟨27388994571642765668452525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36518659428857020891270033 27388994571642765668452525)
          ·
            refine ⟨10270872964366037125669697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27388994571642765668452525 10270872964366037125669697)
            ·
              refine ⟨7703154723274527844252273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10270872964366037125669697 7703154723274527844252273)
              ·
                refine ⟨5777366042455895883189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7703154723274527844252273 5777366042455895883189205)
                ·
                  refine ⟨135407016620060059762247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5777366042455895883189205 135407016620060059762247)
                  ·
                    rfl

theorem cell23_2373338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_2373338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373338 prefixEnd_2373338 := by exact prefixLift 2373338
  have htrace : WordTrace (prefixWord ++ tailWord_2373338) baseStart_2373338 baseEnd_2373338 := by
    simpa [prefixWord, tailWord_2373338, baseEnd_2373338] using wordTrace_append hprefix tailTrace_2373338
  have hstable : (prefixWord ++ tailWord_2373338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373338).length < 2 ^ (prefixWord ++ tailWord_2373338).sum := by decide
  have hdescent : baseEnd_2373338 < baseStart_2373338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373355 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 5]
def baseStart_2373355 : Nat := 118140960795 + 2373355 * 2 ^ 59
def prefixEnd_2373355 : Nat := 4983230072969 + 3 ^ 40 * 2373355 * 2
def baseEnd_2373355 : Nat := 135407986527962996816405

theorem tailTrace_2373355 : CollatzResearch.WordTrace tailWord_2373355 prefixEnd_2373355 135407986527962996816405 := by
  unfold tailWord_2373355
  simp only [CollatzResearch.WordTrace]
  refine ⟨86563368316747646608601519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57708912211165097739067679 86563368316747646608601519)
  ·
    refine ⟨129845052475121469912902279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86563368316747646608601519 129845052475121469912902279)
    ·
      refine ⟨194767578712682204869353419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129845052475121469912902279 194767578712682204869353419)
      ·
        refine ⟨292151368069023307304030129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194767578712682204869353419 292151368069023307304030129)
        ·
          refine ⟨219113526051767480478022597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292151368069023307304030129 219113526051767480478022597)
          ·
            refine ⟨41083786134706402589629237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219113526051767480478022597 41083786134706402589629237)
            ·
              refine ⟨3851604950128725242777741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41083786134706402589629237 3851604950128725242777741)
              ·
                refine ⟨1444351856298271966041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3851604950128725242777741 1444351856298271966041653)
                ·
                  refine ⟨135407986527962996816405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1444351856298271966041653 135407986527962996816405)
                  ·
                    rfl

theorem cell23_2373355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 5].length) (baseStart_2373355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373355 prefixEnd_2373355 := by exact prefixLift 2373355
  have htrace : WordTrace (prefixWord ++ tailWord_2373355) baseStart_2373355 baseEnd_2373355 := by
    simpa [prefixWord, tailWord_2373355, baseEnd_2373355] using wordTrace_append hprefix tailTrace_2373355
  have hstable : (prefixWord ++ tailWord_2373355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373355).length < 2 ^ (prefixWord ++ tailWord_2373355).sum := by decide
  have hdescent : baseEnd_2373355 < baseStart_2373355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373372 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 5]
def baseStart_2373372 : Nat := 118140960795 + 2373372 * 2 ^ 59
def prefixEnd_2373372 : Nat := 4983230072969 + 3 ^ 40 * 2373372 * 2
def baseEnd_2373372 : Nat := 135408956435865933870563

theorem tailTrace_2373372 : CollatzResearch.WordTrace tailWord_2373372 prefixEnd_2373372 135408956435865933870563 := by
  unfold tailWord_2373372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43281994178843029255985185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57709325571790705674646913 43281994178843029255985185)
  ·
    refine ⟨32461495634132271941988889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43281994178843029255985185 32461495634132271941988889)
    ·
      refine ⟨24346121725599203956491667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32461495634132271941988889 24346121725599203956491667)
      ·
        refine ⟨36519182588398805934737501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24346121725599203956491667 36519182588398805934737501)
        ·
          refine ⟨13694693470649552225526563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36519182588398805934737501 13694693470649552225526563)
          ·
            refine ⟨20542040205974328338289845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13694693470649552225526563 20542040205974328338289845)
            ·
              refine ⟨1925816269310093281714673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20542040205974328338289845 1925816269310093281714673)
              ·
                refine ⟨1444362201982569961286005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925816269310093281714673 1444362201982569961286005)
                ·
                  refine ⟨135408956435865933870563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1444362201982569961286005 135408956435865933870563)
                  ·
                    rfl

theorem cell23_2373372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_2373372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373372 prefixEnd_2373372 := by exact prefixLift 2373372
  have htrace : WordTrace (prefixWord ++ tailWord_2373372) baseStart_2373372 baseEnd_2373372 := by
    simpa [prefixWord, tailWord_2373372, baseEnd_2373372] using wordTrace_append hprefix tailTrace_2373372
  have hstable : (prefixWord ++ tailWord_2373372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373372).length < 2 ^ (prefixWord ++ tailWord_2373372).sum := by decide
  have hdescent : baseEnd_2373372 < baseStart_2373372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373383 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2373383 : Nat := 118140960795 + 2373383 * 2 ^ 59
def prefixEnd_2373383 : Nat := 4983230072969 + 3 ^ 40 * 2373383 * 2
def baseEnd_2373383 : Nat := 1218686256209992861797517

theorem tailTrace_2373383 : CollatzResearch.WordTrace tailWord_2373383 prefixEnd_2373383 1218686256209992861797517 := by
  unfold tailWord_2373383
  simp only [CollatzResearch.WordTrace]
  refine ⟨86564389560646207390620803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57709593040430804927080535 86564389560646207390620803)
  ·
    refine ⟨129846584340969311085931205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86564389560646207390620803 129846584340969311085931205)
    ·
      refine ⟨24346234563931745828612101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129846584340969311085931205 24346234563931745828612101)
      ·
        refine ⟨4564918980737202342864769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24346234563931745828612101 4564918980737202342864769)
        ·
          refine ⟨3423689235552901757148577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564918980737202342864769 3423689235552901757148577)
          ·
            refine ⟨2567766926664676317861433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423689235552901757148577 2567766926664676317861433)
            ·
              refine ⟨1925825194998507238396075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567766926664676317861433 1925825194998507238396075)
              ·
                refine ⟨2888737792497760857594113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925825194998507238396075 2888737792497760857594113)
                ·
                  refine ⟨2166553344373320643195585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2888737792497760857594113 2166553344373320643195585)
                  ·
                    refine ⟨1624915008279990482396689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166553344373320643195585 1624915008279990482396689)
                    ·
                      refine ⟨1218686256209992861797517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1624915008279990482396689 1218686256209992861797517)
                      ·
                        rfl

theorem cell23_2373383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2373383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373383 prefixEnd_2373383 := by exact prefixLift 2373383
  have htrace : WordTrace (prefixWord ++ tailWord_2373383) baseStart_2373383 baseEnd_2373383 := by
    simpa [prefixWord, tailWord_2373383, baseEnd_2373383] using wordTrace_append hprefix tailTrace_2373383
  have hstable : (prefixWord ++ tailWord_2373383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373383).length < 2 ^ (prefixWord ++ tailWord_2373383).sum := by decide
  have hdescent : baseEnd_2373383 < baseStart_2373383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373388 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2373388 : Nat := 118140960795 + 2373388 * 2 ^ 59
def prefixEnd_2373388 : Nat := 4983230072969 + 3 ^ 40 * 2373388 * 2
def baseEnd_2373388 : Nat := 1218688823613265342234993

theorem tailTrace_2373388 : CollatzResearch.WordTrace tailWord_2373388 prefixEnd_2373388 1218688823613265342234993 := by
  unfold tailWord_2373388
  simp only [CollatzResearch.WordTrace]
  refine ⟨43282285962814046622276409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57709714617085395496368545 43282285962814046622276409)
  ·
    refine ⟨32461714472110534966707307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43282285962814046622276409 32461714472110534966707307)
    ·
      refine ⟨48692571708165802450060961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32461714472110534966707307 48692571708165802450060961)
      ·
        refine ⟨36519428781124351837545721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48692571708165802450060961 36519428781124351837545721)
        ·
          refine ⟨27389571585843263878159291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36519428781124351837545721 27389571585843263878159291)
          ·
            refine ⟨41084357378764895817238937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27389571585843263878159291 41084357378764895817238937)
            ·
              refine ⟨30813268034073671862929203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41084357378764895817238937 30813268034073671862929203)
              ·
                refine ⟨46219902051110507794393805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30813268034073671862929203 46219902051110507794393805)
                ·
                  refine ⟨17332463269166440422897677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46219902051110507794393805 17332463269166440422897677)
                  ·
                    refine ⟨6499673725937415158586629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17332463269166440422897677 6499673725937415158586629)
                    ·
                      refine ⟨1218688823613265342234993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6499673725937415158586629 1218688823613265342234993)
                      ·
                        rfl

theorem cell23_2373388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2373388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373388 prefixEnd_2373388 := by exact prefixLift 2373388
  have htrace : WordTrace (prefixWord ++ tailWord_2373388) baseStart_2373388 baseEnd_2373388 := by
    simpa [prefixWord, tailWord_2373388, baseEnd_2373388] using wordTrace_append hprefix tailTrace_2373388
  have hstable : (prefixWord ++ tailWord_2373388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373388).length < 2 ^ (prefixWord ++ tailWord_2373388).sum := by decide
  have hdescent : baseEnd_2373388 < baseStart_2373388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373489 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_2373489 : Nat := 118140960795 + 2373489 * 2 ^ 59
def prefixEnd_2373489 : Nat := 4983230072969 + 3 ^ 40 * 2373489 * 2
def baseEnd_2373489 : Nat := 1218740685159369447072029

theorem tailTrace_2373489 : CollatzResearch.WordTrace tailWord_2373489 prefixEnd_2373489 1218740685159369447072029 := by
  unfold tailWord_2373489
  simp only [CollatzResearch.WordTrace]
  refine ⟨86568255698262187493979521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57712170465508124995986347 86568255698262187493979521)
  ·
    refine ⟨64926191773696640620484641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86568255698262187493979521 64926191773696640620484641)
    ·
      refine ⟨48694643830272480465363481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64926191773696640620484641 48694643830272480465363481)
      ·
        refine ⟨36520982872704360349022611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48694643830272480465363481 36520982872704360349022611)
        ·
          refine ⟨54781474309056540523533917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36520982872704360349022611 54781474309056540523533917)
          ·
            refine ⟨20543052865896202696325219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54781474309056540523533917 20543052865896202696325219)
            ·
              refine ⟨30814579298844304044487829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20543052865896202696325219 30814579298844304044487829)
              ·
                refine ⟨1444433404633326752085367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30814579298844304044487829 1444433404633326752085367)
                ·
                  refine ⟨2166650106949990128128051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444433404633326752085367 2166650106949990128128051)
                  ·
                    refine ⟨3249975160424985192192077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166650106949990128128051 3249975160424985192192077)
                    ·
                      refine ⟨1218740685159369447072029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3249975160424985192192077 1218740685159369447072029)
                      ·
                        rfl

theorem cell23_2373489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_2373489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373489 prefixEnd_2373489 := by exact prefixLift 2373489
  have htrace : WordTrace (prefixWord ++ tailWord_2373489) baseStart_2373489 baseEnd_2373489 := by
    simpa [prefixWord, tailWord_2373489, baseEnd_2373489] using wordTrace_append hprefix tailTrace_2373489
  have hstable : (prefixWord ++ tailWord_2373489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373489).length < 2 ^ (prefixWord ++ tailWord_2373489).sum := by decide
  have hdescent : baseEnd_2373489 < baseStart_2373489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373525 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2373525 : Nat := 118140960795 + 2373525 * 2 ^ 59
def prefixEnd_2373525 : Nat := 4983230072969 + 3 ^ 40 * 2373525 * 2
def baseEnd_2373525 : Nat := 1218759170462931306221863

theorem tailTrace_2373525 : CollatzResearch.WordTrace tailWord_2373525 prefixEnd_2373525 1218759170462931306221863 := by
  unfold tailWord_2373525
  simp only [CollatzResearch.WordTrace]
  refine ⟨86569568726131765642290029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57713045817421177094860019 86569568726131765642290029)
  ·
    refine ⟨32463588272299412115858761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86569568726131765642290029 32463588272299412115858761)
    ·
      refine ⟨24347691204224559086894071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32463588272299412115858761 24347691204224559086894071)
      ·
        refine ⟨36521536806336838630341107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24347691204224559086894071 36521536806336838630341107)
        ·
          refine ⟨54782305209505257945511661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36521536806336838630341107 54782305209505257945511661)
          ·
            refine ⟨20543364453564471729566873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54782305209505257945511661 20543364453564471729566873)
            ·
              refine ⟨15407523340173353797175155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20543364453564471729566873 15407523340173353797175155)
              ·
                refine ⟨23111285010260030695762733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15407523340173353797175155 23111285010260030695762733)
                ·
                  refine ⟨8666731878847511510911025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23111285010260030695762733 8666731878847511510911025)
                  ·
                    refine ⟨6500048909135633633183269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8666731878847511510911025 6500048909135633633183269)
                    ·
                      refine ⟨1218759170462931306221863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6500048909135633633183269 1218759170462931306221863)
                      ·
                        rfl

theorem cell23_2373525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2373525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373525 prefixEnd_2373525 := by exact prefixLift 2373525
  have htrace : WordTrace (prefixWord ++ tailWord_2373525) baseStart_2373525 baseEnd_2373525 := by
    simpa [prefixWord, tailWord_2373525, baseEnd_2373525] using wordTrace_append hprefix tailTrace_2373525
  have hstable : (prefixWord ++ tailWord_2373525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373525).length < 2 ^ (prefixWord ++ tailWord_2373525).sum := by decide
  have hdescent : baseEnd_2373525 < baseStart_2373525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373532 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2373532 : Nat := 118140960795 + 2373532 * 2 ^ 59
def prefixEnd_2373532 : Nat := 4983230072969 + 3 ^ 40 * 2373532 * 2
def baseEnd_2373532 : Nat := 1218762764827512778834331

theorem tailTrace_2373532 : CollatzResearch.WordTrace tailWord_2373532 prefixEnd_2373532 1218762764827512778834331 := by
  unfold tailWord_2373532
  simp only [CollatzResearch.WordTrace]
  refine ⟨43284912018553202918897425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57713216024737603891863233 43284912018553202918897425)
  ·
    refine ⟨32463684013914902189173069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43284912018553202918897425 32463684013914902189173069)
    ·
      refine ⟨12173881505218088320939901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32463684013914902189173069 12173881505218088320939901)
      ·
        refine ⟨4565205564456783120352463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12173881505218088320939901 4565205564456783120352463)
        ·
          refine ⟨6847808346685174680528695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565205564456783120352463 6847808346685174680528695)
          ·
            refine ⟨10271712520027762020793043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847808346685174680528695 10271712520027762020793043)
            ·
              refine ⟨15407568780041643031189565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10271712520027762020793043 15407568780041643031189565)
              ·
                refine ⟨5777838292515616136696087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15407568780041643031189565 5777838292515616136696087)
                ·
                  refine ⟨8666757438773424205044131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777838292515616136696087 8666757438773424205044131)
                  ·
                    refine ⟨13000136158160136307566197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8666757438773424205044131 13000136158160136307566197)
                    ·
                      refine ⟨1218762764827512778834331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13000136158160136307566197 1218762764827512778834331)
                      ·
                        rfl

theorem cell23_2373532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2373532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373532 prefixEnd_2373532 := by exact prefixLift 2373532
  have htrace : WordTrace (prefixWord ++ tailWord_2373532) baseStart_2373532 baseEnd_2373532 := by
    simpa [prefixWord, tailWord_2373532, baseEnd_2373532] using wordTrace_append hprefix tailTrace_2373532
  have hstable : (prefixWord ++ tailWord_2373532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373532).length < 2 ^ (prefixWord ++ tailWord_2373532).sum := by decide
  have hdescent : baseEnd_2373532 < baseStart_2373532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373545 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_2373545 : Nat := 118140960795 + 2373545 * 2 ^ 59
def prefixEnd_2373545 : Nat := 4983230072969 + 3 ^ 40 * 2373545 * 2
def baseEnd_2373545 : Nat := 1218769440076021227971771

theorem tailTrace_2373545 : CollatzResearch.WordTrace tailWord_2373545 prefixEnd_2373545 1218769440076021227971771 := by
  unfold tailWord_2373545
  simp only [CollatzResearch.WordTrace]
  refine ⟨86570298186059309058018089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57713532124039539372012059 86570298186059309058018089)
  ·
    refine ⟨64927723639544481793513567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86570298186059309058018089 64927723639544481793513567)
    ·
      refine ⟨97391585459316722690270351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64927723639544481793513567 97391585459316722690270351)
      ·
        refine ⟨146087378188975084035405527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97391585459316722690270351 146087378188975084035405527)
        ·
          refine ⟨219131067283462626053108291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146087378188975084035405527 219131067283462626053108291)
          ·
            refine ⟨328696600925193939079662437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219131067283462626053108291 328696600925193939079662437)
            ·
              refine ⟨61630612673473863577436707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328696600925193939079662437 61630612673473863577436707)
              ·
                refine ⟨92445919010210795366155061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61630612673473863577436707 92445919010210795366155061)
                ·
                  refine ⟨8666804907207262065577037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92445919010210795366155061 8666804907207262065577037)
                  ·
                    refine ⟨3250051840202723274591389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8666804907207262065577037 3250051840202723274591389)
                    ·
                      refine ⟨1218769440076021227971771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250051840202723274591389 1218769440076021227971771)
                      ·
                        rfl

theorem cell23_2373545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_2373545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373545 prefixEnd_2373545 := by exact prefixLift 2373545
  have htrace : WordTrace (prefixWord ++ tailWord_2373545) baseStart_2373545 baseEnd_2373545 := by
    simpa [prefixWord, tailWord_2373545, baseEnd_2373545] using wordTrace_append hprefix tailTrace_2373545
  have hstable : (prefixWord ++ tailWord_2373545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373545).length < 2 ^ (prefixWord ++ tailWord_2373545).sum := by decide
  have hdescent : baseEnd_2373545 < baseStart_2373545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373562 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_2373562 : Nat := 118140960795 + 2373562 * 2 ^ 59
def prefixEnd_2373562 : Nat := 4983230072969 + 3 ^ 40 * 2373562 * 2
def baseEnd_2373562 : Nat := 1218778169247147661459193

theorem tailTrace_2373562 : CollatzResearch.WordTrace tailWord_2373562 prefixEnd_2373562 1218778169247147661459193 := by
  unfold tailWord_2373562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642729556749430240346735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57713945484665147307591293 21642729556749430240346735)
  ·
    refine ⟨32464094335124145360520103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21642729556749430240346735 32464094335124145360520103)
    ·
      refine ⟨48696141502686218040780155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32464094335124145360520103 48696141502686218040780155)
      ·
        refine ⟨73044212254029327061170233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48696141502686218040780155 73044212254029327061170233)
        ·
          refine ⟨54783159190521995295877675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73044212254029327061170233 54783159190521995295877675)
          ·
            refine ⟨82174738785782992943816513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54783159190521995295877675 82174738785782992943816513)
            ·
              refine ⟨61631054089337244707862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82174738785782992943816513 61631054089337244707862385)
              ·
                refine ⟨46223290567002933530896789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61631054089337244707862385 46223290567002933530896789)
                ·
                  refine ⟨2166716745328262509260787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46223290567002933530896789 2166716745328262509260787)
                  ·
                    refine ⟨3250075117992393763891181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166716745328262509260787 3250075117992393763891181)
                    ·
                      refine ⟨1218778169247147661459193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250075117992393763891181 1218778169247147661459193)
                      ·
                        rfl

theorem cell23_2373562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_2373562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373562 prefixEnd_2373562 := by exact prefixLift 2373562
  have htrace : WordTrace (prefixWord ++ tailWord_2373562) baseStart_2373562 baseEnd_2373562 := by
    simpa [prefixWord, tailWord_2373562, baseEnd_2373562] using wordTrace_append hprefix tailTrace_2373562
  have hstable : (prefixWord ++ tailWord_2373562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373562).length < 2 ^ (prefixWord ++ tailWord_2373562).sum := by decide
  have hdescent : baseEnd_2373562 < baseStart_2373562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373566 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2373566 : Nat := 118140960795 + 2373566 * 2 ^ 59
def prefixEnd_2373566 : Nat := 4983230072969 + 3 ^ 40 * 2373566 * 2
def baseEnd_2373566 : Nat := 1218780223169765645809175

theorem tailTrace_2373566 : CollatzResearch.WordTrace tailWord_2373566 prefixEnd_2373566 1218780223169765645809175 := by
  unfold tailWord_2373566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821383014872903705566569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57714042745988819763021701 10821383014872903705566569)
  ·
    refine ⟨8116037261154677779174927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10821383014872903705566569 8116037261154677779174927)
    ·
      refine ⟨12174055891732016668762391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116037261154677779174927 12174055891732016668762391)
      ·
        refine ⟨18261083837598025003143587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174055891732016668762391 18261083837598025003143587)
        ·
          refine ⟨27391625756397037504715381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18261083837598025003143587 27391625756397037504715381)
          ·
            refine ⟨2567964914662222266067067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27391625756397037504715381 2567964914662222266067067)
            ·
              refine ⟨3851947371993333399100601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567964914662222266067067 3851947371993333399100601)
              ·
                refine ⟨2888960528995000049325451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851947371993333399100601 2888960528995000049325451)
                ·
                  refine ⟨4333440793492500073988177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888960528995000049325451 4333440793492500073988177)
                  ·
                    refine ⟨3250080595119375055491133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333440793492500073988177 3250080595119375055491133)
                    ·
                      refine ⟨1218780223169765645809175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250080595119375055491133 1218780223169765645809175)
                      ·
                        rfl

theorem cell23_2373566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2373566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373566 prefixEnd_2373566 := by exact prefixLift 2373566
  have htrace : WordTrace (prefixWord ++ tailWord_2373566) baseStart_2373566 baseEnd_2373566 := by
    simpa [prefixWord, tailWord_2373566, baseEnd_2373566] using wordTrace_append hprefix tailTrace_2373566
  have hstable : (prefixWord ++ tailWord_2373566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373566).length < 2 ^ (prefixWord ++ tailWord_2373566).sum := by decide
  have hdescent : baseEnd_2373566 < baseStart_2373566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373597 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_2373597 : Nat := 118140960795 + 2373597 * 2 ^ 59
def prefixEnd_2373597 : Nat := 4983230072969 + 3 ^ 40 * 2373597 * 2
def baseEnd_2373597 : Nat := 1218796141070055024521533

theorem tailTrace_2373597 : CollatzResearch.WordTrace tailWord_2373597 prefixEnd_2373597 1218796141070055024521533 := by
  unfold tailWord_2373597
  simp only [CollatzResearch.WordTrace]
  refine ⟨86572194781870921938911045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57714796521247281292607363 86572194781870921938911045)
  ·
    refine ⟨16232286521600797863545821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86572194781870921938911045 16232286521600797863545821)
    ·
      refine ⟨6087107445600299198829683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16232286521600797863545821 6087107445600299198829683)
      ·
        refine ⟨9130661168400448798244525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6087107445600299198829683 9130661168400448798244525)
        ·
          refine ⟨3423997938150168299341697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9130661168400448798244525 3423997938150168299341697)
          ·
            refine ⟨2567998453612626224506273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423997938150168299341697 2567998453612626224506273)
            ·
              refine ⟨1925998840209469668379705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567998453612626224506273 1925998840209469668379705)
              ·
                refine ⟨1444499130157102251284779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925998840209469668379705 1444499130157102251284779)
                ·
                  refine ⟨2166748695235653376927169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444499130157102251284779 2166748695235653376927169)
                  ·
                    refine ⟨1625061521426740032695377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166748695235653376927169 1625061521426740032695377)
                    ·
                      refine ⟨1218796141070055024521533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625061521426740032695377 1218796141070055024521533)
                      ·
                        rfl

theorem cell23_2373597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_2373597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373597 prefixEnd_2373597 := by exact prefixLift 2373597
  have htrace : WordTrace (prefixWord ++ tailWord_2373597) baseStart_2373597 baseEnd_2373597 := by
    simpa [prefixWord, tailWord_2373597, baseEnd_2373597] using wordTrace_append hprefix tailTrace_2373597
  have hstable : (prefixWord ++ tailWord_2373597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373597).length < 2 ^ (prefixWord ++ tailWord_2373597).sum := by decide
  have hdescent : baseEnd_2373597 < baseStart_2373597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373625 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 9]
def baseStart_2373625 : Nat := 118140960795 + 2373625 * 2 ^ 59
def prefixEnd_2373625 : Nat := 4983230072969 + 3 ^ 40 * 2373625 * 2
def baseEnd_2373625 : Nat := 135423390947597879441267

theorem tailTrace_2373625 : CollatzResearch.WordTrace tailWord_2373625 prefixEnd_2373625 135423390947597879441267 := by
  unfold tailWord_2373625
  simp only [CollatzResearch.WordTrace]
  refine ⟨86573216025769482720930329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57715477350512988480620219 86573216025769482720930329)
  ·
    refine ⟨64929912019327112040697747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86573216025769482720930329 64929912019327112040697747)
    ·
      refine ⟨97394868028990668061046621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64929912019327112040697747 97394868028990668061046621)
      ·
        refine ⟨36523075510871500522892483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97394868028990668061046621 36523075510871500522892483)
        ·
          refine ⟨54784613266307250784338725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36523075510871500522892483 54784613266307250784338725)
          ·
            refine ⟨10272114987432609522063511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54784613266307250784338725 10272114987432609522063511)
            ·
              refine ⟨15408172481148914283095267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272114987432609522063511 15408172481148914283095267)
              ·
                refine ⟨23112258721723371424642901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15408172481148914283095267 23112258721723371424642901)
                ·
                  refine ⟨135423390947597879441267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23112258721723371424642901 135423390947597879441267)
                  ·
                    rfl

theorem cell23_2373625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_2373625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373625 prefixEnd_2373625 := by exact prefixLift 2373625
  have htrace : WordTrace (prefixWord ++ tailWord_2373625) baseStart_2373625 baseEnd_2373625 := by
    simpa [prefixWord, tailWord_2373625, baseEnd_2373625] using wordTrace_append hprefix tailTrace_2373625
  have hstable : (prefixWord ++ tailWord_2373625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373625).length < 2 ^ (prefixWord ++ tailWord_2373625).sum := by decide
  have hdescent : baseEnd_2373625 < baseStart_2373625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373692 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2373692 : Nat := 118140960795 + 2373692 * 2 ^ 59
def prefixEnd_2373692 : Nat := 4983230072969 + 3 ^ 40 * 2373692 * 2
def baseEnd_2373692 : Nat := 1218844921732232152833595

theorem tailTrace_2373692 : CollatzResearch.WordTrace tailWord_2373692 prefixEnd_2373692 1218844921732232152833595 := by
  unfold tailWord_2373692
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287829858263376581809665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57717106477684502109079553 43287829858263376581809665)
  ·
    refine ⟨32465872393697532436357249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43287829858263376581809665 32465872393697532436357249)
    ·
      refine ⟨24349404295273149327267937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32465872393697532436357249 24349404295273149327267937)
      ·
        refine ⟨18262053221454861995450953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24349404295273149327267937 18262053221454861995450953)
        ·
          refine ⟨13696539916091146496588215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18262053221454861995450953 13696539916091146496588215)
          ·
            refine ⟨20544809874136719744882323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13696539916091146496588215 20544809874136719744882323)
            ·
              refine ⟨30817214811205079617323485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20544809874136719744882323 30817214811205079617323485)
              ·
                refine ⟨11556455554201904856496307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30817214811205079617323485 11556455554201904856496307)
                ·
                  refine ⟨17334683331302857284744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11556455554201904856496307 17334683331302857284744461)
                  ·
                    refine ⟨6500506249238571481779173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17334683331302857284744461 6500506249238571481779173)
                    ·
                      refine ⟨1218844921732232152833595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6500506249238571481779173 1218844921732232152833595)
                      ·
                        rfl

theorem cell23_2373692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2373692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373692 prefixEnd_2373692 := by exact prefixLift 2373692
  have htrace : WordTrace (prefixWord ++ tailWord_2373692) baseStart_2373692 baseEnd_2373692 := by
    simpa [prefixWord, tailWord_2373692, baseEnd_2373692] using wordTrace_append hprefix tailTrace_2373692
  have hstable : (prefixWord ++ tailWord_2373692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373692).length < 2 ^ (prefixWord ++ tailWord_2373692).sum := by decide
  have hdescent : baseEnd_2373692 < baseStart_2373692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373715 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 12]
def baseStart_2373715 : Nat := 118140960795 + 2373715 * 2 ^ 59
def prefixEnd_2373715 : Nat := 4983230072969 + 3 ^ 40 * 2373715 * 2
def baseEnd_2373715 : Nat := 135428525754142840316221

theorem tailTrace_2373715 : CollatzResearch.WordTrace tailWord_2373715 prefixEnd_2373715 135428525754142840316221 := by
  unfold tailWord_2373715
  simp only [CollatzResearch.WordTrace]
  refine ⟨86576498595443428091706599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57717665730295618727804399 86576498595443428091706599)
  ·
    refine ⟨129864747893165142137559899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86576498595443428091706599 129864747893165142137559899)
    ·
      refine ⟨194797121839747713206339849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129864747893165142137559899 194797121839747713206339849)
      ·
        refine ⟨146097841379810784904754887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194797121839747713206339849 146097841379810784904754887)
        ·
          refine ⟨219146762069716177357132331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146097841379810784904754887 219146762069716177357132331)
          ·
            refine ⟨328720143104574266035698497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219146762069716177357132331 328720143104574266035698497)
            ·
              refine ⟨246540107328430699526773873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328720143104574266035698497 246540107328430699526773873)
              ·
                refine ⟨184905080496323024645080405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246540107328430699526773873 184905080496323024645080405)
                ·
                  refine ⟨135428525754142840316221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 184905080496323024645080405 135428525754142840316221)
                  ·
                    rfl

theorem cell23_2373715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 12].length) (baseStart_2373715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373715 prefixEnd_2373715 := by exact prefixLift 2373715
  have htrace : WordTrace (prefixWord ++ tailWord_2373715) baseStart_2373715 baseEnd_2373715 := by
    simpa [prefixWord, tailWord_2373715, baseEnd_2373715] using wordTrace_append hprefix tailTrace_2373715
  have hstable : (prefixWord ++ tailWord_2373715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373715).length < 2 ^ (prefixWord ++ tailWord_2373715).sum := by decide
  have hdescent : baseEnd_2373715 < baseStart_2373715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373719 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 3, 4]
def baseStart_2373719 : Nat := 118140960795 + 2373719 * 2 ^ 59
def prefixEnd_2373719 : Nat := 4983230072969 + 3 ^ 40 * 2373719 * 2
def baseEnd_2373719 : Nat := 406286261903301182398657

theorem tailTrace_2373719 : CollatzResearch.WordTrace tailWord_2373719 prefixEnd_2373719 406286261903301182398657 := by
  unfold tailWord_2373719
  simp only [CollatzResearch.WordTrace]
  refine ⟨86576644487428936774852211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57717762991619291183234807 86576644487428936774852211)
  ·
    refine ⟨129864966731143405162278317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86576644487428936774852211 129864966731143405162278317)
    ·
      refine ⟨48699362524178776935854369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129864966731143405162278317 48699362524178776935854369)
      ·
        refine ⟨36524521893134082701890777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48699362524178776935854369 36524521893134082701890777)
        ·
          refine ⟨27393391419850562026418083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36524521893134082701890777 27393391419850562026418083)
          ·
            refine ⟨41090087129775843039627125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27393391419850562026418083 41090087129775843039627125)
            ·
              refine ⟨3852195668416485284965043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41090087129775843039627125 3852195668416485284965043)
              ·
                refine ⟨5778293502624727927447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852195668416485284965043 5778293502624727927447565)
                ·
                  refine ⟨2166860063484272972792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5778293502624727927447565 2166860063484272972792837)
                  ·
                    refine ⟨406286261903301182398657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166860063484272972792837 406286261903301182398657)
                    ·
                      rfl

theorem cell23_2373719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_2373719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373719 prefixEnd_2373719 := by exact prefixLift 2373719
  have htrace : WordTrace (prefixWord ++ tailWord_2373719) baseStart_2373719 baseEnd_2373719 := by
    simpa [prefixWord, tailWord_2373719, baseEnd_2373719] using wordTrace_append hprefix tailTrace_2373719
  have hstable : (prefixWord ++ tailWord_2373719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373719).length < 2 ^ (prefixWord ++ tailWord_2373719).sum := by decide
  have hdescent : baseEnd_2373719 < baseStart_2373719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373746 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2373746 : Nat := 118140960795 + 2373746 * 2 ^ 59
def prefixEnd_2373746 : Nat := 4983230072969 + 3 ^ 40 * 2373746 * 2
def baseEnd_2373746 : Nat := 1218872649687574941558347

theorem tailTrace_2373746 : CollatzResearch.WordTrace tailWord_2373746 prefixEnd_2373746 1218872649687574941558347 := by
  unfold tailWord_2373746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644407314582780096521273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57718419505554080257390061 21644407314582780096521273)
  ·
    refine ⟨16233305485937085072390955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21644407314582780096521273 16233305485937085072390955)
    ·
      refine ⟨24349958228905627608586433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16233305485937085072390955 24349958228905627608586433)
      ·
        refine ⟨18262468671679220706439825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24349958228905627608586433 18262468671679220706439825)
        ·
          refine ⟨13696851503759415529829869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18262468671679220706439825 13696851503759415529829869)
          ·
            refine ⟨5136319313909780823686201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13696851503759415529829869 5136319313909780823686201)
            ·
              refine ⟨3852239485432335617764651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136319313909780823686201 3852239485432335617764651)
              ·
                refine ⟨5778359228148503426646977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852239485432335617764651 5778359228148503426646977)
                ·
                  refine ⟨4333769421111377569985233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5778359228148503426646977 4333769421111377569985233)
                  ·
                    refine ⟨3250327065833533177488925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333769421111377569985233 3250327065833533177488925)
                    ·
                      refine ⟨1218872649687574941558347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250327065833533177488925 1218872649687574941558347)
                      ·
                        rfl

theorem cell23_2373746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2373746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373746 prefixEnd_2373746 := by exact prefixLift 2373746
  have htrace : WordTrace (prefixWord ++ tailWord_2373746) baseStart_2373746 baseEnd_2373746 := by
    simpa [prefixWord, tailWord_2373746, baseEnd_2373746] using wordTrace_append hprefix tailTrace_2373746
  have hstable : (prefixWord ++ tailWord_2373746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373746).length < 2 ^ (prefixWord ++ tailWord_2373746).sum := by decide
  have hdescent : baseEnd_2373746 < baseStart_2373746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373770 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_2373770 : Nat := 118140960795 + 2373770 * 2 ^ 59
def prefixEnd_2373770 : Nat := 4983230072969 + 3 ^ 40 * 2373770 * 2
def baseEnd_2373770 : Nat := 406294991074427615886079

theorem tailTrace_2373770 : CollatzResearch.WordTrace tailWord_2373770 prefixEnd_2373770 406294991074427615886079 := by
  unfold tailWord_2373770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644626152561043121239691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57719003073496114989972509 21644626152561043121239691)
  ·
    refine ⟨32466939228841564681859537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21644626152561043121239691 32466939228841564681859537)
    ·
      refine ⟨24350204421631173511394653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32466939228841564681859537 24350204421631173511394653)
      ·
        refine ⟨9131326658111690066772995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24350204421631173511394653 9131326658111690066772995)
        ·
          refine ⟨13696989987167535100159493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131326658111690066772995 13696989987167535100159493)
          ·
            refine ⟨2568185622593912831279905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13696989987167535100159493 2568185622593912831279905)
            ·
              refine ⟨1926139216945434623459929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568185622593912831279905 1926139216945434623459929)
              ·
                refine ⟨1444604412709075967594947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926139216945434623459929 1444604412709075967594947)
                ·
                  refine ⟨2166906619063613951392421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444604412709075967594947 2166906619063613951392421)
                  ·
                    refine ⟨406294991074427615886079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166906619063613951392421 406294991074427615886079)
                    ·
                      rfl

theorem cell23_2373770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_2373770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373770 prefixEnd_2373770 := by exact prefixLift 2373770
  have htrace : WordTrace (prefixWord ++ tailWord_2373770) baseStart_2373770 baseEnd_2373770 := by
    simpa [prefixWord, tailWord_2373770, baseEnd_2373770] using wordTrace_append hprefix tailTrace_2373770
  have hstable : (prefixWord ++ tailWord_2373770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373770).length < 2 ^ (prefixWord ++ tailWord_2373770).sum := by decide
  have hdescent : baseEnd_2373770 < baseStart_2373770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373813 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2373813 : Nat := 118140960795 + 2373813 * 2 ^ 59
def prefixEnd_2373813 : Nat := 4983230072969 + 3 ^ 40 * 2373813 * 2
def baseEnd_2373813 : Nat := 406302350963808726473513

theorem tailTrace_2373813 : CollatzResearch.WordTrace tailWord_2373813 prefixEnd_2373813 406302350963808726473513 := by
  unfold tailWord_2373813
  simp only [CollatzResearch.WordTrace]
  refine ⟨86580072949088390828774093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57720048632725593885849395 86580072949088390828774093)
  ·
    refine ⟨32467527355908146560790285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86580072949088390828774093 32467527355908146560790285)
    ·
      refine ⟨12175322758465554960296357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32467527355908146560790285 12175322758465554960296357)
      ·
        refine ⟨2282873017212291555055567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12175322758465554960296357 2282873017212291555055567)
        ·
          refine ⟨3424309525818437332583351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282873017212291555055567 3424309525818437332583351)
          ·
            refine ⟨5136464288727655998875027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424309525818437332583351 5136464288727655998875027)
            ·
              refine ⟨7704696433091483998312541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136464288727655998875027 7704696433091483998312541)
              ·
                refine ⟨2889261162409306499367203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7704696433091483998312541 2889261162409306499367203)
                ·
                  refine ⟨4333891743613959749050805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889261162409306499367203 4333891743613959749050805)
                  ·
                    refine ⟨406302350963808726473513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4333891743613959749050805 406302350963808726473513)
                    ·
                      rfl

theorem cell23_2373813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2373813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373813 prefixEnd_2373813 := by exact prefixLift 2373813
  have htrace : WordTrace (prefixWord ++ tailWord_2373813) baseStart_2373813 baseEnd_2373813 := by
    simpa [prefixWord, tailWord_2373813, baseEnd_2373813] using wordTrace_append hprefix tailTrace_2373813
  have hstable : (prefixWord ++ tailWord_2373813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373813).length < 2 ^ (prefixWord ++ tailWord_2373813).sum := by decide
  have hdescent : baseEnd_2373813 < baseStart_2373813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373816 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_2373816 : Nat := 118140960795 + 2373816 * 2 ^ 59
def prefixEnd_2373816 : Nat := 4983230072969 + 3 ^ 40 * 2373816 * 2
def baseEnd_2373816 : Nat := 1218908593333389667683025

theorem tailTrace_2373816 : CollatzResearch.WordTrace tailWord_2373816 prefixEnd_2373816 1218908593333389667683025 := by
  unfold tailWord_2373816
  simp only [CollatzResearch.WordTrace]
  refine ⟨43290091184038761170566651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57720121578718348227422201 43290091184038761170566651)
  ·
    refine ⟨64935136776058141755849977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43290091184038761170566651 64935136776058141755849977)
    ·
      refine ⟨48701352582043606316887483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64935136776058141755849977 48701352582043606316887483)
      ·
        refine ⟨73052028873065409475331225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48701352582043606316887483 73052028873065409475331225)
        ·
          refine ⟨54789021654799057106498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73052028873065409475331225 54789021654799057106498419)
          ·
            refine ⟨82183532482198585659747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54789021654799057106498419 82183532482198585659747629)
            ·
              refine ⟨30818824680824469622405361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82183532482198585659747629 30818824680824469622405361)
              ·
                refine ⟨23114118510618352216804021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30818824680824469622405361 23114118510618352216804021)
                ·
                  refine ⟨2166948610370470520325377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23114118510618352216804021 2166948610370470520325377)
                  ·
                    refine ⟨1625211457777852890244033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166948610370470520325377 1625211457777852890244033)
                    ·
                      refine ⟨1218908593333389667683025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625211457777852890244033 1218908593333389667683025)
                      ·
                        rfl

theorem cell23_2373816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_2373816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373816 prefixEnd_2373816 := by exact prefixLift 2373816
  have htrace : WordTrace (prefixWord ++ tailWord_2373816) baseStart_2373816 baseEnd_2373816 := by
    simpa [prefixWord, tailWord_2373816, baseEnd_2373816] using wordTrace_append hprefix tailTrace_2373816
  have hstable : (prefixWord ++ tailWord_2373816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373816).length < 2 ^ (prefixWord ++ tailWord_2373816).sum := by decide
  have hdescent : baseEnd_2373816 < baseStart_2373816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2373832 : Nat := 118140960795 + 2373832 * 2 ^ 59
def prefixEnd_2373832 : Nat := 4983230072969 + 3 ^ 40 * 2373832 * 2
def baseEnd_2373832 : Nat := 1218916809023861605082951

theorem tailTrace_2373832 : CollatzResearch.WordTrace tailWord_2373832 prefixEnd_2373832 1218916809023861605082951 := by
  unfold tailWord_2373832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43290382968009778536857875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57720510624013038049143833 43290382968009778536857875)
  ·
    refine ⟨64935574452014667805286813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43290382968009778536857875 64935574452014667805286813)
    ·
      refine ⟨24350840419505500426982555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64935574452014667805286813 24350840419505500426982555)
      ·
        refine ⟨36526260629258250640473833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24350840419505500426982555 36526260629258250640473833)
        ·
          refine ⟨27394695471943687980355375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36526260629258250640473833 27394695471943687980355375)
          ·
            refine ⟨41092043207915531970533063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27394695471943687980355375 41092043207915531970533063)
            ·
              refine ⟨61638064811873297955799595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41092043207915531970533063 61638064811873297955799595)
              ·
                refine ⟨92457097217809946933699393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61638064811873297955799595 92457097217809946933699393)
                ·
                  refine ⟨69342822913357460200274545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92457097217809946933699393 69342822913357460200274545)
                  ·
                    refine ⟨52007117185018095150205909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69342822913357460200274545 52007117185018095150205909)
                    ·
                      refine ⟨1218916809023861605082951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52007117185018095150205909 1218916809023861605082951)
                      ·
                        rfl

theorem cell23_2373832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2373832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373832 prefixEnd_2373832 := by exact prefixLift 2373832
  have htrace : WordTrace (prefixWord ++ tailWord_2373832) baseStart_2373832 baseEnd_2373832 := by
    simpa [prefixWord, tailWord_2373832, baseEnd_2373832] using wordTrace_append hprefix tailTrace_2373832
  have hstable : (prefixWord ++ tailWord_2373832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373832).length < 2 ^ (prefixWord ++ tailWord_2373832).sum := by decide
  have hdescent : baseEnd_2373832 < baseStart_2373832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373853 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2373853 : Nat := 118140960795 + 2373853 * 2 ^ 59
def prefixEnd_2373853 : Nat := 4983230072969 + 3 ^ 40 * 2373853 * 2
def baseEnd_2373853 : Nat := 1218927592117606022920355

theorem tailTrace_2373853 : CollatzResearch.WordTrace tailWord_2373853 prefixEnd_2373853 1218927592117606022920355 := by
  unfold tailWord_2373853
  simp only [CollatzResearch.WordTrace]
  refine ⟨86581531868943477660230213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57721021245962318440153475 86581531868943477660230213)
  ·
    refine ⟨16234037225426902061293165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86581531868943477660230213 16234037225426902061293165)
    ·
      refine ⟨6087763959535088272984937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16234037225426902061293165 6087763959535088272984937)
      ·
        refine ⟨4565822969651316204738703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087763959535088272984937 4565822969651316204738703)
        ·
          refine ⟨6848734454476974307108055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565822969651316204738703 6848734454476974307108055)
          ·
            refine ⟨10273101681715461460662083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848734454476974307108055 10273101681715461460662083)
            ·
              refine ⟨15409652522573192190993125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10273101681715461460662083 15409652522573192190993125)
              ·
                refine ⟨2889309847982473535811211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15409652522573192190993125 2889309847982473535811211)
                ·
                  refine ⟨4333964771973710303716817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889309847982473535811211 4333964771973710303716817)
                  ·
                    refine ⟨3250473578980282727787613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333964771973710303716817 3250473578980282727787613)
                    ·
                      refine ⟨1218927592117606022920355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250473578980282727787613 1218927592117606022920355)
                      ·
                        rfl

theorem cell23_2373853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2373853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373853 prefixEnd_2373853 := by exact prefixLift 2373853
  have htrace : WordTrace (prefixWord ++ tailWord_2373853) baseStart_2373853 baseEnd_2373853 := by
    simpa [prefixWord, tailWord_2373853, baseEnd_2373853] using wordTrace_append hprefix tailTrace_2373853
  have hstable : (prefixWord ++ tailWord_2373853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373853).length < 2 ^ (prefixWord ++ tailWord_2373853).sum := by decide
  have hdescent : baseEnd_2373853 < baseStart_2373853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373866 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2373866 : Nat := 118140960795 + 2373866 * 2 ^ 59
def prefixEnd_2373866 : Nat := 4983230072969 + 3 ^ 40 * 2373866 * 2
def baseEnd_2373866 : Nat := 1218934267366114472057795

theorem tailTrace_2373866 : CollatzResearch.WordTrace tailWord_2373866 prefixEnd_2373866 1218934267366114472057795 := by
  unfold tailWord_2373866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645501504474095220113363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57721337345264253920302301 21645501504474095220113363)
  ·
    refine ⟨32468252256711142830170045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21645501504474095220113363 32468252256711142830170045)
    ·
      refine ⟨12175594596266678561313767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32468252256711142830170045 12175594596266678561313767)
      ·
        refine ⟨18263391894400017841970651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175594596266678561313767 18263391894400017841970651)
        ·
          refine ⟨27395087841600026762955977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263391894400017841970651 27395087841600026762955977)
          ·
            refine ⟨20546315881200020072216983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27395087841600026762955977 20546315881200020072216983)
            ·
              refine ⟨30819473821800030108325475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20546315881200020072216983 30819473821800030108325475)
              ·
                refine ⟨46229210732700045162488213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30819473821800030108325475 46229210732700045162488213)
                ·
                  refine ⟨2166994253095314616991635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46229210732700045162488213 2166994253095314616991635)
                  ·
                    refine ⟨3250491379642971925487453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166994253095314616991635 3250491379642971925487453)
                    ·
                      refine ⟨1218934267366114472057795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3250491379642971925487453 1218934267366114472057795)
                      ·
                        rfl

theorem cell23_2373866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2373866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373866 prefixEnd_2373866 := by exact prefixLift 2373866
  have htrace : WordTrace (prefixWord ++ tailWord_2373866) baseStart_2373866 baseEnd_2373866 := by
    simpa [prefixWord, tailWord_2373866, baseEnd_2373866] using wordTrace_append hprefix tailTrace_2373866
  have hstable : (prefixWord ++ tailWord_2373866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373866).length < 2 ^ (prefixWord ++ tailWord_2373866).sum := by decide
  have hdescent : baseEnd_2373866 < baseStart_2373866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373872 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2373872 : Nat := 118140960795 + 2373872 * 2 ^ 59
def prefixEnd_2373872 : Nat := 4983230072969 + 3 ^ 40 * 2373872 * 2
def baseEnd_2373872 : Nat := 1218937348250041448582767

theorem tailTrace_2373872 : CollatzResearch.WordTrace tailWord_2373872 prefixEnd_2373872 1218937348250041448582767 := by
  unfold tailWord_2373872
  simp only [CollatzResearch.WordTrace]
  refine ⟨43291112427937321952585935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57721483237249762603447913 43291112427937321952585935)
  ·
    refine ⟨64936668641905982928878903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43291112427937321952585935 64936668641905982928878903)
    ·
      refine ⟨97405002962858974393318355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64936668641905982928878903 97405002962858974393318355)
      ·
        refine ⟨146107504444288461589977533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97405002962858974393318355 146107504444288461589977533)
        ·
          refine ⟨54790314166608173096241575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146107504444288461589977533 54790314166608173096241575)
          ·
            refine ⟨82185471249912259644362363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54790314166608173096241575 82185471249912259644362363)
            ·
              refine ⟨123278206874868389466543545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82185471249912259644362363 123278206874868389466543545)
              ·
                refine ⟨92458655156151292099907659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123278206874868389466543545 92458655156151292099907659)
                ·
                  refine ⟨138687982734226938149861489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92458655156151292099907659 138687982734226938149861489)
                  ·
                    refine ⟨104015987050670203612396117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138687982734226938149861489 104015987050670203612396117)
                    ·
                      refine ⟨1218937348250041448582767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 104015987050670203612396117 1218937348250041448582767)
                      ·
                        rfl

theorem cell23_2373872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2373872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373872 prefixEnd_2373872 := by exact prefixLift 2373872
  have htrace : WordTrace (prefixWord ++ tailWord_2373872) baseStart_2373872 baseEnd_2373872 := by
    simpa [prefixWord, tailWord_2373872, baseEnd_2373872] using wordTrace_append hprefix tailTrace_2373872
  have hstable : (prefixWord ++ tailWord_2373872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373872).length < 2 ^ (prefixWord ++ tailWord_2373872).sum := by decide
  have hdescent : baseEnd_2373872 < baseStart_2373872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373889 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2373889 : Nat := 118140960795 + 2373889 * 2 ^ 59
def prefixEnd_2373889 : Nat := 4983230072969 + 3 ^ 40 * 2373889 * 2
def baseEnd_2373889 : Nat := 1218946077421167882070189

theorem tailTrace_2373889 : CollatzResearch.WordTrace tailWord_2373889 prefixEnd_2373889 1218946077421167882070189 := by
  unfold tailWord_2373889
  simp only [CollatzResearch.WordTrace]
  refine ⟨86582844896813055808540721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57721896597875370539027147 86582844896813055808540721)
  ·
    refine ⟨64937133672609791856405541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86582844896813055808540721 64937133672609791856405541)
    ·
      refine ⟨12175712563614335973076039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64937133672609791856405541 12175712563614335973076039)
      ·
        refine ⟨18263568845421503959614059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175712563614335973076039 18263568845421503959614059)
        ·
          refine ⟨27395353268132255939421089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263568845421503959614059 27395353268132255939421089)
          ·
            refine ⟨20546514951099191954565817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27395353268132255939421089 20546514951099191954565817)
            ·
              refine ⟨15409886213324393965924363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20546514951099191954565817 15409886213324393965924363)
              ·
                refine ⟨23114829319986590948886545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15409886213324393965924363 23114829319986590948886545)
                ·
                  refine ⟨17336121989989943211664909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23114829319986590948886545 17336121989989943211664909)
                  ·
                    refine ⟨6501045746246228704374341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17336121989989943211664909 6501045746246228704374341)
                    ·
                      refine ⟨1218946077421167882070189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6501045746246228704374341 1218946077421167882070189)
                      ·
                        rfl

theorem cell23_2373889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2373889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373889 prefixEnd_2373889 := by exact prefixLift 2373889
  have htrace : WordTrace (prefixWord ++ tailWord_2373889) baseStart_2373889 baseEnd_2373889 := by
    simpa [prefixWord, tailWord_2373889, baseEnd_2373889] using wordTrace_append hprefix tailTrace_2373889
  have hstable : (prefixWord ++ tailWord_2373889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373889).length < 2 ^ (prefixWord ++ tailWord_2373889).sum := by decide
  have hdescent : baseEnd_2373889 < baseStart_2373889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373909 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2373909 : Nat := 118140960795 + 2373909 * 2 ^ 59
def prefixEnd_2373909 : Nat := 4983230072969 + 3 ^ 40 * 2373909 * 2
def baseEnd_2373909 : Nat := 1218956347034257803820097

theorem tailTrace_2373909 : CollatzResearch.WordTrace tailWord_2373909 prefixEnd_2373909 1218956347034257803820097 := by
  unfold tailWord_2373909
  simp only [CollatzResearch.WordTrace]
  refine ⟨86583574356740599224268781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57722382904493732816179187 86583574356740599224268781)
  ·
    refine ⟨32468840383777724709100793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86583574356740599224268781 32468840383777724709100793)
    ·
      refine ⟨24351630287833293531825595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32468840383777724709100793 24351630287833293531825595)
      ·
        refine ⟨36527445431749940297738393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24351630287833293531825595 36527445431749940297738393)
        ·
          refine ⟨27395584073812455223303795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36527445431749940297738393 27395584073812455223303795)
          ·
            refine ⟨41093376110718682834955693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27395584073812455223303795 41093376110718682834955693)
            ·
              refine ⟨15410016041519506063108385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41093376110718682834955693 15410016041519506063108385)
              ·
                refine ⟨11557512031139629547331289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15410016041519506063108385 11557512031139629547331289)
                ·
                  refine ⟨8668134023354722160498467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11557512031139629547331289 8668134023354722160498467)
                  ·
                    refine ⟨13002201035032083240747701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8668134023354722160498467 13002201035032083240747701)
                    ·
                      refine ⟨1218956347034257803820097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13002201035032083240747701 1218956347034257803820097)
                      ·
                        rfl

theorem cell23_2373909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2373909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373909 prefixEnd_2373909 := by exact prefixLift 2373909
  have htrace : WordTrace (prefixWord ++ tailWord_2373909) baseStart_2373909 baseEnd_2373909 := by
    simpa [prefixWord, tailWord_2373909, baseEnd_2373909] using wordTrace_append hprefix tailTrace_2373909
  have hstable : (prefixWord ++ tailWord_2373909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373909).length < 2 ^ (prefixWord ++ tailWord_2373909).sum := by decide
  have hdescent : baseEnd_2373909 < baseStart_2373909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373953 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2373953 : Nat := 118140960795 + 2373953 * 2 ^ 59
def prefixEnd_2373953 : Nat := 4983230072969 + 3 ^ 40 * 2373953 * 2
def baseEnd_2373953 : Nat := 1218978940183055631669895

theorem tailTrace_2373953 : CollatzResearch.WordTrace tailWord_2373953 prefixEnd_2373953 1218978940183055631669895 := by
  unfold tailWord_2373953
  simp only [CollatzResearch.WordTrace]
  refine ⟨86585179168581194738870513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57723452779054129825913675 86585179168581194738870513)
  ·
    refine ⟨64938884376435896054152885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86585179168581194738870513 64938884376435896054152885)
    ·
      refine ⟨6088020410290865255076833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64938884376435896054152885 6088020410290865255076833)
      ·
        refine ⟨4566015307718148941307625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6088020410290865255076833 4566015307718148941307625)
        ·
          refine ⟨3424511480788611705980719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4566015307718148941307625 3424511480788611705980719)
          ·
            refine ⟨5136767221182917558971079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424511480788611705980719 5136767221182917558971079)
            ·
              refine ⟨7705150831774376338456619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136767221182917558971079 7705150831774376338456619)
              ·
                refine ⟨11557726247661564507684929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705150831774376338456619 11557726247661564507684929)
                ·
                  refine ⟨8668294685746173380763697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11557726247661564507684929 8668294685746173380763697)
                  ·
                    refine ⟨6501221014309630035572773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8668294685746173380763697 6501221014309630035572773)
                    ·
                      refine ⟨1218978940183055631669895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6501221014309630035572773 1218978940183055631669895)
                      ·
                        rfl

theorem cell23_2373953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2373953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373953 prefixEnd_2373953 := by exact prefixLift 2373953
  have htrace : WordTrace (prefixWord ++ tailWord_2373953) baseStart_2373953 baseEnd_2373953 := by
    simpa [prefixWord, tailWord_2373953, baseEnd_2373953] using wordTrace_append hprefix tailTrace_2373953
  have hstable : (prefixWord ++ tailWord_2373953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373953).length < 2 ^ (prefixWord ++ tailWord_2373953).sum := by decide
  have hdescent : baseEnd_2373953 < baseStart_2373953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373959 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 7]
def baseStart_2373959 : Nat := 118140960795 + 2373959 * 2 ^ 59
def prefixEnd_2373959 : Nat := 4983230072969 + 3 ^ 40 * 2373959 * 2
def baseEnd_2373959 : Nat := 406327340355660869398289

theorem tailTrace_2373959 : CollatzResearch.WordTrace tailWord_2373959 prefixEnd_2373959 406327340355660869398289 := by
  unfold tailWord_2373959
  simp only [CollatzResearch.WordTrace]
  refine ⟨86585398006559457763588931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57723598671039638509059287 86585398006559457763588931)
  ·
    refine ⟨129878097009839186645383397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86585398006559457763588931 129878097009839186645383397)
    ·
      refine ⟨24352143189344847496009387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129878097009839186645383397 24352143189344847496009387)
      ·
        refine ⟨36528214784017271244014081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24352143189344847496009387 36528214784017271244014081)
        ·
          refine ⟨27396161088012953433010561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36528214784017271244014081 27396161088012953433010561)
          ·
            refine ⟨20547120816009715074757921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27396161088012953433010561 20547120816009715074757921)
            ·
              refine ⟨15410340612007286306068441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20547120816009715074757921 15410340612007286306068441)
              ·
                refine ⟨11557755459005464729551331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15410340612007286306068441 11557755459005464729551331)
                ·
                  refine ⟨17336633188508197094326997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11557755459005464729551331 17336633188508197094326997)
                  ·
                    refine ⟨406327340355660869398289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17336633188508197094326997 406327340355660869398289)
                    ·
                      rfl

theorem cell23_2373959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_2373959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2373959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2373959 prefixEnd_2373959 := by exact prefixLift 2373959
  have htrace : WordTrace (prefixWord ++ tailWord_2373959) baseStart_2373959 baseEnd_2373959 := by
    simpa [prefixWord, tailWord_2373959, baseEnd_2373959] using wordTrace_append hprefix tailTrace_2373959
  have hstable : (prefixWord ++ tailWord_2373959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373959).length < 2 ^ (prefixWord ++ tailWord_2373959).sum := by decide
  have hdescent : baseEnd_2373959 < baseStart_2373959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374009 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2374009 : Nat := 118140960795 + 2374009 * 2 ^ 59
def prefixEnd_2374009 : Nat := 4983230072969 + 3 ^ 40 * 2374009 * 2
def baseEnd_2374009 : Nat := 1219007695099707412569637

theorem tailTrace_2374009 : CollatzResearch.WordTrace tailWord_2374009 prefixEnd_2374009 1219007695099707412569637 := by
  unfold tailWord_2374009
  simp only [CollatzResearch.WordTrace]
  refine ⟨86587221656378316302909081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57724814437585544201939387 86587221656378316302909081)
  ·
    refine ⟨64940416242283737227181811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86587221656378316302909081 64940416242283737227181811)
    ·
      refine ⟨97410624363425605840772717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64940416242283737227181811 97410624363425605840772717)
      ·
        refine ⟨36528984136284602190289769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97410624363425605840772717 36528984136284602190289769)
        ·
          refine ⟨27396738102213451642717327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36528984136284602190289769 27396738102213451642717327)
          ·
            refine ⟨41095107153320177464075991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27396738102213451642717327 41095107153320177464075991)
            ·
              refine ⟨61642660729980266196113987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41095107153320177464075991 61642660729980266196113987)
              ·
                refine ⟨92463991094970399294170981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61642660729980266196113987 92463991094970399294170981)
                ·
                  refine ⟨17336998330306949867657059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92463991094970399294170981 17336998330306949867657059)
                  ·
                    refine ⟨26005497495460424801485589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17336998330306949867657059 26005497495460424801485589)
                    ·
                      refine ⟨1219007695099707412569637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26005497495460424801485589 1219007695099707412569637)
                      ·
                        rfl

theorem cell23_2374009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2374009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374009 prefixEnd_2374009 := by exact prefixLift 2374009
  have htrace : WordTrace (prefixWord ++ tailWord_2374009) baseStart_2374009 baseEnd_2374009 := by
    simpa [prefixWord, tailWord_2374009, baseEnd_2374009] using wordTrace_append hprefix tailTrace_2374009
  have hstable : (prefixWord ++ tailWord_2374009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374009).length < 2 ^ (prefixWord ++ tailWord_2374009).sum := by decide
  have hdescent : baseEnd_2374009 < baseStart_2374009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374013 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_2374013 : Nat := 118140960795 + 2374013 * 2 ^ 59
def prefixEnd_2374013 : Nat := 4983230072969 + 3 ^ 40 * 2374013 * 2
def baseEnd_2374013 : Nat := 1219009749022325396919619

theorem tailTrace_2374013 : CollatzResearch.WordTrace tailWord_2374013 prefixEnd_2374013 1219009749022325396919619 := by
  unfold tailWord_2374013
  simp only [CollatzResearch.WordTrace]
  refine ⟨86587367548363824986054693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57724911698909216657369795 86587367548363824986054693)
  ·
    refine ⟨16235131415318217184885255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86587367548363824986054693 16235131415318217184885255)
    ·
      refine ⟨24352697122977325777327883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16235131415318217184885255 24352697122977325777327883)
      ·
        refine ⟨36529045684465988665991825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24352697122977325777327883 36529045684465988665991825)
        ·
          refine ⟨27396784263349491499493869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36529045684465988665991825 27396784263349491499493869)
          ·
            refine ⟨10273794098756059312310201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27396784263349491499493869 10273794098756059312310201)
            ·
              refine ⟨7705345574067044484232651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10273794098756059312310201 7705345574067044484232651)
              ·
                refine ⟨11558018361100566726348977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705345574067044484232651 11558018361100566726348977)
                ·
                  refine ⟨8668513770825425044761733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558018361100566726348977 8668513770825425044761733)
                  ·
                    refine ⟨1625346332029767195892825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8668513770825425044761733 1625346332029767195892825)
                    ·
                      refine ⟨1219009749022325396919619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625346332029767195892825 1219009749022325396919619)
                      ·
                        rfl

theorem cell23_2374013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_2374013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374013 prefixEnd_2374013 := by exact prefixLift 2374013
  have htrace : WordTrace (prefixWord ++ tailWord_2374013) baseStart_2374013 baseEnd_2374013 := by
    simpa [prefixWord, tailWord_2374013, baseEnd_2374013] using wordTrace_append hprefix tailTrace_2374013
  have hstable : (prefixWord ++ tailWord_2374013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374013).length < 2 ^ (prefixWord ++ tailWord_2374013).sum := by decide
  have hdescent : baseEnd_2374013 < baseStart_2374013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374066 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_2374066 : Nat := 118140960795 + 2374066 * 2 ^ 59
def prefixEnd_2374066 : Nat := 4983230072969 + 3 ^ 40 * 2374066 * 2
def baseEnd_2374066 : Nat := 406345654499004563185625

theorem tailTrace_2374066 : CollatzResearch.WordTrace tailWord_2374066 prefixEnd_2374066 406345654499004563185625 := by
  unfold tailWord_2374066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647325154292953759433513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57726200411447876691822701 21647325154292953759433513)
  ·
    refine ⟨16235493865719715319575135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21647325154292953759433513 16235493865719715319575135)
    ·
      refine ⟨24353240798579572979362703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16235493865719715319575135 24353240798579572979362703)
      ·
        refine ⟨36529861197869359469044055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24353240798579572979362703 36529861197869359469044055)
        ·
          refine ⟨54794791796804039203566083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36529861197869359469044055 54794791796804039203566083)
          ·
            refine ⟨82192187695206058805349125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54794791796804039203566083 82192187695206058805349125)
            ·
              refine ⟨15411035192851136026002961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82192187695206058805349125 15411035192851136026002961)
              ·
                refine ⟨11558276394638352019502221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15411035192851136026002961 11558276394638352019502221)
                ·
                  refine ⟨4334353647989382007313333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11558276394638352019502221 4334353647989382007313333)
                  ·
                    refine ⟨406345654499004563185625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4334353647989382007313333 406345654499004563185625)
                    ·
                      rfl

theorem cell23_2374066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_2374066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374066 prefixEnd_2374066 := by exact prefixLift 2374066
  have htrace : WordTrace (prefixWord ++ tailWord_2374066) baseStart_2374066 baseEnd_2374066 := by
    simpa [prefixWord, tailWord_2374066, baseEnd_2374066] using wordTrace_append hprefix tailTrace_2374066
  have hstable : (prefixWord ++ tailWord_2374066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374066).length < 2 ^ (prefixWord ++ tailWord_2374066).sum := by decide
  have hdescent : baseEnd_2374066 < baseStart_2374066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374090 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_2374090 : Nat := 118140960795 + 2374090 * 2 ^ 59
def prefixEnd_2374090 : Nat := 4983230072969 + 3 ^ 40 * 2374090 * 2
def baseEnd_2374090 : Nat := 1219049287032721595656765

theorem tailTrace_2374090 : CollatzResearch.WordTrace tailWord_2374090 prefixEnd_2374090 1219049287032721595656765 := by
  unfold tailWord_2374090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647543992271216784151931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57726783979389911424405149 21647543992271216784151931)
  ·
    refine ⟨32471315988406825176227897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21647543992271216784151931 32471315988406825176227897)
    ·
      refine ⟨24353486991305118882170923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32471315988406825176227897 24353486991305118882170923)
      ·
        refine ⟨36530230486957678323256385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24353486991305118882170923 36530230486957678323256385)
        ·
          refine ⟨27397672865218258742442289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36530230486957678323256385 27397672865218258742442289)
          ·
            refine ⟨20548254648913694056831717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27397672865218258742442289 20548254648913694056831717)
            ·
              refine ⟨3852797746671317635655947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20548254648913694056831717 3852797746671317635655947)
              ·
                refine ⟨5779196620006976453483921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852797746671317635655947 5779196620006976453483921)
                ·
                  refine ⟨4334397465005232340112941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779196620006976453483921 4334397465005232340112941)
                  ·
                    refine ⟨1625399049376962127542353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4334397465005232340112941 1625399049376962127542353)
                    ·
                      refine ⟨1219049287032721595656765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625399049376962127542353 1219049287032721595656765)
                      ·
                        rfl

theorem cell23_2374090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_2374090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374090 prefixEnd_2374090 := by exact prefixLift 2374090
  have htrace : WordTrace (prefixWord ++ tailWord_2374090) baseStart_2374090 baseEnd_2374090 := by
    simpa [prefixWord, tailWord_2374090, baseEnd_2374090] using wordTrace_append hprefix tailTrace_2374090
  have hstable : (prefixWord ++ tailWord_2374090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374090).length < 2 ^ (prefixWord ++ tailWord_2374090).sum := by decide
  have hdescent : baseEnd_2374090 < baseStart_2374090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374130 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_2374130 : Nat := 118140960795 + 2374130 * 2 ^ 59
def prefixEnd_2374130 : Nat := 4983230072969 + 3 ^ 40 * 2374130 * 2
def baseEnd_2374130 : Nat := 406356608752967146385527

theorem tailTrace_2374130 : CollatzResearch.WordTrace tailWord_2374130 prefixEnd_2374130 406356608752967146385527 := by
  unfold tailWord_2374130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647908722234988492015961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57727756592626635978709229 21647908722234988492015961)
  ·
    refine ⟨16235931541676241369011971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21647908722234988492015961 16235931541676241369011971)
    ·
      refine ⟨24353897312514362053517957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16235931541676241369011971 24353897312514362053517957)
      ·
        refine ⟨4566355746096442885034617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24353897312514362053517957 4566355746096442885034617)
        ·
          refine ⟨3424766809572332163775963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4566355746096442885034617 3424766809572332163775963)
          ·
            refine ⟨5137150214358498245663945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424766809572332163775963 5137150214358498245663945)
            ·
              refine ⟨3852862660768873684247959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5137150214358498245663945 3852862660768873684247959)
              ·
                refine ⟨5779293991153310526371939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852862660768873684247959 5779293991153310526371939)
                ·
                  refine ⟨8668940986729965789557909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779293991153310526371939 8668940986729965789557909)
                  ·
                    refine ⟨406356608752967146385527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8668940986729965789557909 406356608752967146385527)
                    ·
                      rfl

theorem cell23_2374130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_2374130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374130 prefixEnd_2374130 := by exact prefixLift 2374130
  have htrace : WordTrace (prefixWord ++ tailWord_2374130) baseStart_2374130 baseEnd_2374130 := by
    simpa [prefixWord, tailWord_2374130, baseEnd_2374130] using wordTrace_append hprefix tailTrace_2374130
  have hstable : (prefixWord ++ tailWord_2374130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374130).length < 2 ^ (prefixWord ++ tailWord_2374130).sum := by decide
  have hdescent : baseEnd_2374130 < baseStart_2374130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374154 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_2374154 : Nat := 118140960795 + 2374154 * 2 ^ 59
def prefixEnd_2374154 : Nat := 4983230072969 + 3 ^ 40 * 2374154 * 2
def baseEnd_2374154 : Nat := 1219082149794609345256471

theorem tailTrace_2374154 : CollatzResearch.WordTrace tailWord_2374154 prefixEnd_2374154 1219082149794609345256471 := by
  unfold tailWord_2374154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21648127560213251516734379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57728340160568670711291677 21648127560213251516734379)
  ·
    refine ⟨32472191340319877275101569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21648127560213251516734379 32472191340319877275101569)
    ·
      refine ⟨24354143505239907956326177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32472191340319877275101569 24354143505239907956326177)
      ·
        refine ⟨18265607628929930967244633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24354143505239907956326177 18265607628929930967244633)
        ·
          refine ⟨13699205721697448225433475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18265607628929930967244633 13699205721697448225433475)
          ·
            refine ⟨20548808582546172338150213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13699205721697448225433475 20548808582546172338150213)
            ·
              refine ⟨3852901609227407313403165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20548808582546172338150213 3852901609227407313403165)
              ·
                refine ⟨1444838103460277742526187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3852901609227407313403165 1444838103460277742526187)
                ·
                  refine ⟨2167257155190416613789281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444838103460277742526187 2167257155190416613789281)
                  ·
                    refine ⟨1625442866392812460341961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2167257155190416613789281 1625442866392812460341961)
                    ·
                      refine ⟨1219082149794609345256471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625442866392812460341961 1219082149794609345256471)
                      ·
                        rfl

theorem cell23_2374154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_2374154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374154 prefixEnd_2374154 := by exact prefixLift 2374154
  have htrace : WordTrace (prefixWord ++ tailWord_2374154) baseStart_2374154 baseEnd_2374154 := by
    simpa [prefixWord, tailWord_2374154, baseEnd_2374154] using wordTrace_append hprefix tailTrace_2374154
  have hstable : (prefixWord ++ tailWord_2374154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374154).length < 2 ^ (prefixWord ++ tailWord_2374154).sum := by decide
  have hdescent : baseEnd_2374154 < baseStart_2374154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374164 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2374164 : Nat := 118140960795 + 2374164 * 2 ^ 59
def prefixEnd_2374164 : Nat := 4983230072969 + 3 ^ 40 * 2374164 * 2
def baseEnd_2374164 : Nat := 406362428200384768710475

theorem tailTrace_2374164 : CollatzResearch.WordTrace tailWord_2374164 prefixEnd_2374164 406362428200384768710475 := by
  unfold tailWord_2374164
  simp only [CollatzResearch.WordTrace]
  refine ⟨43296437485408388887400773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57728583313877851849867697 43296437485408388887400773)
  ·
    refine ⟨8118082028514072916387645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43296437485408388887400773 8118082028514072916387645)
    ·
      refine ⟨3044280760692777343645367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8118082028514072916387645 3044280760692777343645367)
      ·
        refine ⟨4566421141039166015468051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044280760692777343645367 4566421141039166015468051)
        ·
          refine ⟨6849631711558749023202077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566421141039166015468051 6849631711558749023202077)
          ·
            refine ⟨2568611891834530883700779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6849631711558749023202077 2568611891834530883700779)
            ·
              refine ⟨3852917837751796325551169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568611891834530883700779 3852917837751796325551169)
              ·
                refine ⟨2889688378313847244163377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852917837751796325551169 2889688378313847244163377)
                ·
                  refine ⟨2167266283735385433122533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889688378313847244163377 2167266283735385433122533)
                  ·
                    refine ⟨406362428200384768710475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2167266283735385433122533 406362428200384768710475)
                    ·
                      rfl

theorem cell23_2374164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2374164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374164 prefixEnd_2374164 := by exact prefixLift 2374164
  have htrace : WordTrace (prefixWord ++ tailWord_2374164) baseStart_2374164 baseEnd_2374164 := by
    simpa [prefixWord, tailWord_2374164, baseEnd_2374164] using wordTrace_append hprefix tailTrace_2374164
  have hstable : (prefixWord ++ tailWord_2374164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374164).length < 2 ^ (prefixWord ++ tailWord_2374164).sum := by decide
  have hdescent : baseEnd_2374164 < baseStart_2374164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374197 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2374197 : Nat := 118140960795 + 2374197 * 2 ^ 59
def prefixEnd_2374197 : Nat := 4983230072969 + 3 ^ 40 * 2374197 * 2
def baseEnd_2374197 : Nat := 1219104229462752677018773

theorem tailTrace_2374197 : CollatzResearch.WordTrace tailWord_2374197 prefixEnd_2374197 1219104229462752677018773 := by
  unfold tailWord_2374197
  simp only [CollatzResearch.WordTrace]
  refine ⟨86594078579697224410752845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57729385719798149607168563 86594078579697224410752845)
  ·
    refine ⟨32472779467386459154032317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86594078579697224410752845 32472779467386459154032317)
    ·
      refine ⟨12177292300269922182762119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32472779467386459154032317 12177292300269922182762119)
      ·
        refine ⟨18265938450404883274143179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12177292300269922182762119 18265938450404883274143179)
        ·
          refine ⟨27398907675607324911214769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18265938450404883274143179 27398907675607324911214769)
          ·
            refine ⟨20549180756705493683411077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27398907675607324911214769 20549180756705493683411077)
            ·
              refine ⟨3852971391882280065639577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20549180756705493683411077 3852971391882280065639577)
              ·
                refine ⟨2889728543911710049229683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852971391882280065639577 2889728543911710049229683)
                ·
                  refine ⟨4334592815867565073844525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889728543911710049229683 4334592815867565073844525)
                  ·
                    refine ⟨1625472305950336902691697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4334592815867565073844525 1625472305950336902691697)
                    ·
                      refine ⟨1219104229462752677018773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625472305950336902691697 1219104229462752677018773)
                      ·
                        rfl

theorem cell23_2374197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2374197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374197 prefixEnd_2374197 := by exact prefixLift 2374197
  have htrace : WordTrace (prefixWord ++ tailWord_2374197) baseStart_2374197 baseEnd_2374197 := by
    simpa [prefixWord, tailWord_2374197, baseEnd_2374197] using wordTrace_append hprefix tailTrace_2374197
  have hstable : (prefixWord ++ tailWord_2374197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374197).length < 2 ^ (prefixWord ++ tailWord_2374197).sum := by decide
  have hdescent : baseEnd_2374197 < baseStart_2374197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374213 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_2374213 : Nat := 118140960795 + 2374213 * 2 ^ 59
def prefixEnd_2374213 : Nat := 4983230072969 + 3 ^ 40 * 2374213 * 2
def baseEnd_2374213 : Nat := 1219112445153224614418699

theorem tailTrace_2374213 : CollatzResearch.WordTrace tailWord_2374213 prefixEnd_2374213 1219112445153224614418699 := by
  unfold tailWord_2374213
  simp only [CollatzResearch.WordTrace]
  refine ⟨86594662147639259143335293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57729774765092839428890195 86594662147639259143335293)
  ·
    refine ⟨32472998305364722178750735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86594662147639259143335293 32472998305364722178750735)
    ·
      refine ⟨48709497458047083268126103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32472998305364722178750735 48709497458047083268126103)
      ·
        refine ⟨73064246187070624902189155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48709497458047083268126103 73064246187070624902189155)
        ·
          refine ⟨109596369280605937353283733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73064246187070624902189155 109596369280605937353283733)
          ·
            refine ⟨5137329810028403313435175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109596369280605937353283733 5137329810028403313435175)
            ·
              refine ⟨7705994715042604970152763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137329810028403313435175 7705994715042604970152763)
              ·
                refine ⟨11558992072563907455229145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705994715042604970152763 11558992072563907455229145)
                ·
                  refine ⟨8669244054422930591421859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558992072563907455229145 8669244054422930591421859)
                  ·
                    refine ⟨13003866081634395887132789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8669244054422930591421859 13003866081634395887132789)
                    ·
                      refine ⟨1219112445153224614418699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13003866081634395887132789 1219112445153224614418699)
                      ·
                        rfl

theorem cell23_2374213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_2374213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374213 prefixEnd_2374213 := by exact prefixLift 2374213
  have htrace : WordTrace (prefixWord ++ tailWord_2374213) baseStart_2374213 baseEnd_2374213 := by
    simpa [prefixWord, tailWord_2374213, baseEnd_2374213] using wordTrace_append hprefix tailTrace_2374213
  have hstable : (prefixWord ++ tailWord_2374213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374213).length < 2 ^ (prefixWord ++ tailWord_2374213).sum := by decide
  have hdescent : baseEnd_2374213 < baseStart_2374213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374216 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 9]
def baseStart_2374216 : Nat := 118140960795 + 2374216 * 2 ^ 59
def prefixEnd_2374216 : Nat := 4983230072969 + 3 ^ 40 * 2374216 * 2
def baseEnd_2374216 : Nat := 135457109510576455853465

theorem tailTrace_2374216 : CollatzResearch.WordTrace tailWord_2374216 prefixEnd_2374216 135457109510576455853465 := by
  unfold tailWord_2374216
  simp only [CollatzResearch.WordTrace]
  refine ⟨43297385783314195327847251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57729847711085593770463001 43297385783314195327847251)
  ·
    refine ⟨64946078674971292991770877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43297385783314195327847251 64946078674971292991770877)
    ·
      refine ⟨24354779503114234871914079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64946078674971292991770877 24354779503114234871914079)
      ·
        refine ⟨36532169254671352307871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24354779503114234871914079 36532169254671352307871119)
        ·
          refine ⟨54798253882007028461806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36532169254671352307871119 54798253882007028461806679)
          ·
            refine ⟨82197380823010542692710019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54798253882007028461806679 82197380823010542692710019)
            ·
              refine ⟨123296071234515814039065029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82197380823010542692710019 123296071234515814039065029)
              ·
                refine ⟨23118013356471715132324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123296071234515814039065029 23118013356471715132324693)
                ·
                  refine ⟨135457109510576455853465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23118013356471715132324693 135457109510576455853465)
                  ·
                    rfl

theorem cell23_2374216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_2374216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374216 prefixEnd_2374216 := by exact prefixLift 2374216
  have htrace : WordTrace (prefixWord ++ tailWord_2374216) baseStart_2374216 baseEnd_2374216 := by
    simpa [prefixWord, tailWord_2374216, baseEnd_2374216] using wordTrace_append hprefix tailTrace_2374216
  have hstable : (prefixWord ++ tailWord_2374216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374216).length < 2 ^ (prefixWord ++ tailWord_2374216).sum := by decide
  have hdescent : baseEnd_2374216 < baseStart_2374216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374238 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2374238 : Nat := 118140960795 + 2374238 * 2 ^ 59
def prefixEnd_2374238 : Nat := 4983230072969 + 3 ^ 40 * 2374238 * 2
def baseEnd_2374238 : Nat := 1219125282169587016606085

theorem tailTrace_2374238 : CollatzResearch.WordTrace tailWord_2374238 prefixEnd_2374238 1219125282169587016606085 := by
  unfold tailWord_2374238
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824446746568586051624421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57730382648365792275330245 10824446746568586051624421)
  ·
    refine ⟨2029583764981609884679579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10824446746568586051624421 2029583764981609884679579)
    ·
      refine ⟨3044375647472414827019369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029583764981609884679579 3044375647472414827019369)
      ·
        refine ⟨2283281735604311120264527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044375647472414827019369 2283281735604311120264527)
        ·
          refine ⟨3424922603406466680396791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283281735604311120264527 3424922603406466680396791)
          ·
            refine ⟨5137383905109700020595187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424922603406466680396791 5137383905109700020595187)
            ·
              refine ⟨7706075857664550030892781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137383905109700020595187 7706075857664550030892781)
              ·
                refine ⟨2889778446624206261584793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7706075857664550030892781 2889778446624206261584793)
                ·
                  refine ⟨2167333834968154696188595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889778446624206261584793 2167333834968154696188595)
                  ·
                    refine ⟨3251000752452232044282893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2167333834968154696188595 3251000752452232044282893)
                    ·
                      refine ⟨1219125282169587016606085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251000752452232044282893 1219125282169587016606085)
                      ·
                        rfl

theorem cell23_2374238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2374238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374238 prefixEnd_2374238 := by exact prefixLift 2374238
  have htrace : WordTrace (prefixWord ++ tailWord_2374238) baseStart_2374238 baseEnd_2374238 := by
    simpa [prefixWord, tailWord_2374238, baseEnd_2374238] using wordTrace_append hprefix tailTrace_2374238
  have hstable : (prefixWord ++ tailWord_2374238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374238).length < 2 ^ (prefixWord ++ tailWord_2374238).sum := by decide
  have hdescent : baseEnd_2374238 < baseStart_2374238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374243 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2374243 : Nat := 118140960795 + 2374243 * 2 ^ 59
def prefixEnd_2374243 : Nat := 4983230072969 + 3 ^ 40 * 2374243 * 2
def baseEnd_2374243 : Nat := 1219127849572859497043561

theorem tailTrace_2374243 : CollatzResearch.WordTrace tailWord_2374243 prefixEnd_2374243 1219127849572859497043561 := by
  unfold tailWord_2374243
  simp only [CollatzResearch.WordTrace]
  refine ⟨86595756337530574266927383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57730504225020382844618255 86595756337530574266927383)
  ·
    refine ⟨129893634506295861400391075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86595756337530574266927383 129893634506295861400391075)
    ·
      refine ⟨194840451759443792100586613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129893634506295861400391075 194840451759443792100586613)
      ·
        refine ⟨18266292352447855509429995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194840451759443792100586613 18266292352447855509429995)
        ·
          refine ⟨27399438528671783264144993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18266292352447855509429995 27399438528671783264144993)
          ·
            refine ⟨20549578896503837448108745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27399438528671783264144993 20549578896503837448108745)
            ·
              refine ⟨15412184172377878086081559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20549578896503837448108745 15412184172377878086081559)
              ·
                refine ⟨23118276258566817129122339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15412184172377878086081559 23118276258566817129122339)
                ·
                  refine ⟨34677414387850225693683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23118276258566817129122339 34677414387850225693683509)
                  ·
                    refine ⟨3251007598860958658782829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34677414387850225693683509 3251007598860958658782829)
                    ·
                      refine ⟨1219127849572859497043561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251007598860958658782829 1219127849572859497043561)
                      ·
                        rfl

theorem cell23_2374243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2374243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374243 prefixEnd_2374243 := by exact prefixLift 2374243
  have htrace : WordTrace (prefixWord ++ tailWord_2374243) baseStart_2374243 baseEnd_2374243 := by
    simpa [prefixWord, tailWord_2374243, baseEnd_2374243] using wordTrace_append hprefix tailTrace_2374243
  have hstable : (prefixWord ++ tailWord_2374243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374243).length < 2 ^ (prefixWord ++ tailWord_2374243).sum := by decide
  have hdescent : baseEnd_2374243 < baseStart_2374243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374263 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 2, 5]
def baseStart_2374263 : Nat := 118140960795 + 2374263 * 2 ^ 59
def prefixEnd_2374263 : Nat := 4983230072969 + 3 ^ 40 * 2374263 * 2
def baseEnd_2374263 : Nat := 406379373061983139597823

theorem tailTrace_2374263 : CollatzResearch.WordTrace tailWord_2374263 prefixEnd_2374263 406379373061983139597823 := by
  unfold tailWord_2374263
  simp only [CollatzResearch.WordTrace]
  refine ⟨86596485797458117682655443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57730990531638745121770295 86596485797458117682655443)
  ·
    refine ⟨129894728696187176523983165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86596485797458117682655443 129894728696187176523983165)
    ·
      refine ⟨48710523261070191196493687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129894728696187176523983165 48710523261070191196493687)
      ·
        refine ⟨73065784891605286794740531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48710523261070191196493687 73065784891605286794740531)
        ·
          refine ⟨109598677337407930192110797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73065784891605286794740531 109598677337407930192110797)
          ·
            refine ⟨41099504001527973822041549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109598677337407930192110797 41099504001527973822041549)
            ·
              refine ⟨15412314000572990183265581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41099504001527973822041549 15412314000572990183265581)
              ·
                refine ⟨5779617750214871318724593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15412314000572990183265581 5779617750214871318724593)
                ·
                  refine ⟨4334713312661153489043445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779617750214871318724593 4334713312661153489043445)
                  ·
                    refine ⟨406379373061983139597823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4334713312661153489043445 406379373061983139597823)
                    ·
                      rfl

theorem cell23_2374263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_2374263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374263 prefixEnd_2374263 := by exact prefixLift 2374263
  have htrace : WordTrace (prefixWord ++ tailWord_2374263) baseStart_2374263 baseEnd_2374263 := by
    simpa [prefixWord, tailWord_2374263, baseEnd_2374263] using wordTrace_append hprefix tailTrace_2374263
  have hstable : (prefixWord ++ tailWord_2374263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374263).length < 2 ^ (prefixWord ++ tailWord_2374263).sum := by decide
  have hdescent : baseEnd_2374263 < baseStart_2374263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374273 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2374273 : Nat := 118140960795 + 2374273 * 2 ^ 59
def prefixEnd_2374273 : Nat := 4983230072969 + 3 ^ 40 * 2374273 * 2
def baseEnd_2374273 : Nat := 1219143253992494379668423

theorem tailTrace_2374273 : CollatzResearch.WordTrace tailWord_2374273 prefixEnd_2374273 1219143253992494379668423 := by
  unfold tailWord_2374273
  simp only [CollatzResearch.WordTrace]
  refine ⟨86596850527421889390519473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57731233684947926260346315 86596850527421889390519473)
  ·
    refine ⟨64947637895566417042889605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86596850527421889390519473 64947637895566417042889605)
    ·
      refine ⟨12177682105418703195541801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64947637895566417042889605 12177682105418703195541801)
      ·
        refine ⟨9133261579064027396656351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12177682105418703195541801 9133261579064027396656351)
        ·
          refine ⟨13699892368596041094984527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133261579064027396656351 13699892368596041094984527)
          ·
            refine ⟨20549838552894061642476791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13699892368596041094984527 20549838552894061642476791)
            ·
              refine ⟨30824757829341092463715187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20549838552894061642476791 30824757829341092463715187)
              ·
                refine ⟨46237136744011638695572781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30824757829341092463715187 46237136744011638695572781)
                ·
                  refine ⟨17338926279004364510839793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46237136744011638695572781 17338926279004364510839793)
                  ·
                    refine ⟨13004194709253273383129845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17338926279004364510839793 13004194709253273383129845)
                    ·
                      refine ⟨1219143253992494379668423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13004194709253273383129845 1219143253992494379668423)
                      ·
                        rfl

theorem cell23_2374273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2374273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374273 prefixEnd_2374273 := by exact prefixLift 2374273
  have htrace : WordTrace (prefixWord ++ tailWord_2374273) baseStart_2374273 baseEnd_2374273 := by
    simpa [prefixWord, tailWord_2374273, baseEnd_2374273] using wordTrace_append hprefix tailTrace_2374273
  have hstable : (prefixWord ++ tailWord_2374273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374273).length < 2 ^ (prefixWord ++ tailWord_2374273).sum := by decide
  have hdescent : baseEnd_2374273 < baseStart_2374273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374283 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4]
def baseStart_2374283 : Nat := 118140960795 + 2374283 * 2 ^ 59
def prefixEnd_2374283 : Nat := 4983230072969 + 3 ^ 40 * 2374283 * 2
def baseEnd_2374283 : Nat := 1219148388799039340543377

theorem tailTrace_2374283 : CollatzResearch.WordTrace tailWord_2374283 prefixEnd_2374283 1219148388799039340543377 := by
  unfold tailWord_2374283
  simp only [CollatzResearch.WordTrace]
  refine ⟨86597215257385661098383503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57731476838257107398922335 86597215257385661098383503)
  ·
    refine ⟨129895822886078491647575255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86597215257385661098383503 129895822886078491647575255)
    ·
      refine ⟨194843734329117737471362883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129895822886078491647575255 194843734329117737471362883)
      ·
        refine ⟨292265601493676606207044325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194843734329117737471362883 292265601493676606207044325)
        ·
          refine ⟨54799800280064363663820811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292265601493676606207044325 54799800280064363663820811)
          ·
            refine ⟨82199700420096545495731217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54799800280064363663820811 82199700420096545495731217)
            ·
              refine ⟨61649775315072409121798413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82199700420096545495731217 61649775315072409121798413)
              ·
                refine ⟨23118665743152153420674405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61649775315072409121798413 23118665743152153420674405)
                ·
                  refine ⟨4334749826841028766376451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23118665743152153420674405 4334749826841028766376451)
                  ·
                    refine ⟨6502124740261543149564677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334749826841028766376451 6502124740261543149564677)
                    ·
                      refine ⟨1219148388799039340543377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6502124740261543149564677 1219148388799039340543377)
                      ·
                        rfl

theorem cell23_2374283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_2374283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374283 prefixEnd_2374283 := by exact prefixLift 2374283
  have htrace : WordTrace (prefixWord ++ tailWord_2374283) baseStart_2374283 baseEnd_2374283 := by
    simpa [prefixWord, tailWord_2374283, baseEnd_2374283] using wordTrace_append hprefix tailTrace_2374283
  have hstable : (prefixWord ++ tailWord_2374283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374283).length < 2 ^ (prefixWord ++ tailWord_2374283).sum := by decide
  have hdescent : baseEnd_2374283 < baseStart_2374283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374290 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2374290 : Nat := 118140960795 + 2374290 * 2 ^ 59
def prefixEnd_2374290 : Nat := 4983230072969 + 3 ^ 40 * 2374290 * 2
def baseEnd_2374290 : Nat := 1219151983163620813155845

theorem tailTrace_2374290 : CollatzResearch.WordTrace tailWord_2374290 prefixEnd_2374290 1219151983163620813155845 := by
  unfold tailWord_2374290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649367642090075323472081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57731647045573534195925549 21649367642090075323472081)
  ·
    refine ⟨16237025731567556492604061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21649367642090075323472081 16237025731567556492604061)
    ·
      refine ⟨6088884649337833684726523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16237025731567556492604061 6088884649337833684726523)
      ·
        refine ⟨9133326974006750527089785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088884649337833684726523 9133326974006750527089785)
        ·
          refine ⟨6849995230505062895317339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9133326974006750527089785 6849995230505062895317339)
          ·
            refine ⟨10274992845757594342976009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6849995230505062895317339 10274992845757594342976009)
            ·
              refine ⟨7706244634318195757232007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10274992845757594342976009 7706244634318195757232007)
              ·
                refine ⟨11559366951477293635848011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706244634318195757232007 11559366951477293635848011)
                ·
                  refine ⟨17339050427215940453772017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11559366951477293635848011 17339050427215940453772017)
                  ·
                    refine ⟨13004287820411955340329013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17339050427215940453772017 13004287820411955340329013)
                    ·
                      refine ⟨1219151983163620813155845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13004287820411955340329013 1219151983163620813155845)
                      ·
                        rfl

theorem cell23_2374290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2374290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374290 prefixEnd_2374290 := by exact prefixLift 2374290
  have htrace : WordTrace (prefixWord ++ tailWord_2374290) baseStart_2374290 baseEnd_2374290 := by
    simpa [prefixWord, tailWord_2374290, baseEnd_2374290] using wordTrace_append hprefix tailTrace_2374290
  have hstable : (prefixWord ++ tailWord_2374290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374290).length < 2 ^ (prefixWord ++ tailWord_2374290).sum := by decide
  have hdescent : baseEnd_2374290 < baseStart_2374290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374317 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2374317 : Nat := 118140960795 + 2374317 * 2 ^ 59
def prefixEnd_2374317 : Nat := 4983230072969 + 3 ^ 40 * 2374317 * 2
def baseEnd_2374317 : Nat := 1219165847141292207518221

theorem tailTrace_2374317 : CollatzResearch.WordTrace tailWord_2374317 prefixEnd_2374317 1219165847141292207518221 := by
  unfold tailWord_2374317
  simp only [CollatzResearch.WordTrace]
  refine ⟨86598455339262484905121205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57732303559508323270080803 86598455339262484905121205)
  ·
    refine ⟨8118605188055857959855113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86598455339262484905121205 8118605188055857959855113)
    ·
      refine ⟨6088953891041893469891335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8118605188055857959855113 6088953891041893469891335)
      ·
        refine ⟨9133430836562840204837003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088953891041893469891335 9133430836562840204837003)
        ·
          refine ⟨13700146254844260307255505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133430836562840204837003 13700146254844260307255505)
          ·
            refine ⟨10275109691133195230441629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13700146254844260307255505 10275109691133195230441629)
            ·
              refine ⟨3853166134174948211415611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10275109691133195230441629 3853166134174948211415611)
              ·
                refine ⟨5779749201262422317123417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853166134174948211415611 5779749201262422317123417)
                ·
                  refine ⟨4334811900946816737842563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779749201262422317123417 4334811900946816737842563)
                  ·
                    refine ⟨6502217851420225106763845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334811900946816737842563 6502217851420225106763845)
                    ·
                      refine ⟨1219165847141292207518221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6502217851420225106763845 1219165847141292207518221)
                      ·
                        rfl

theorem cell23_2374317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2374317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374317 prefixEnd_2374317 := by exact prefixLift 2374317
  have htrace : WordTrace (prefixWord ++ tailWord_2374317) baseStart_2374317 baseEnd_2374317 := by
    simpa [prefixWord, tailWord_2374317, baseEnd_2374317] using wordTrace_append hprefix tailTrace_2374317
  have hstable : (prefixWord ++ tailWord_2374317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374317).length < 2 ^ (prefixWord ++ tailWord_2374317).sum := by decide
  have hdescent : baseEnd_2374317 < baseStart_2374317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374340 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2374340 : Nat := 118140960795 + 2374340 * 2 ^ 59
def prefixEnd_2374340 : Nat := 4983230072969 + 3 ^ 40 * 2374340 * 2
def baseEnd_2374340 : Nat := 135464184132927290836735

theorem tailTrace_2374340 : CollatzResearch.WordTrace tailWord_2374340 prefixEnd_2374340 135464184132927290836735 := by
  unfold tailWord_2374340
  simp only [CollatzResearch.WordTrace]
  refine ⟨43299647109089579916604237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57732862812119439888805649 43299647109089579916604237)
  ·
    refine ⟨16237367665908592468726589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43299647109089579916604237 16237367665908592468726589)
    ·
      refine ⟨6089012874715722175772471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16237367665908592468726589 6089012874715722175772471)
      ·
        refine ⟨9133519312073583263658707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6089012874715722175772471 9133519312073583263658707)
        ·
          refine ⟨13700278968110374895488061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133519312073583263658707 13700278968110374895488061)
          ·
            refine ⟨5137604613041390585808023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13700278968110374895488061 5137604613041390585808023)
            ·
              refine ⟨7706406919562085878712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137604613041390585808023 7706406919562085878712035)
              ·
                refine ⟨11559610379343128818068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706406919562085878712035 11559610379343128818068053)
                ·
                  refine ⟨135464184132927290836735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11559610379343128818068053 135464184132927290836735)
                  ·
                    rfl

theorem cell23_2374340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2374340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374340 prefixEnd_2374340 := by exact prefixLift 2374340
  have htrace : WordTrace (prefixWord ++ tailWord_2374340) baseStart_2374340 baseEnd_2374340 := by
    simpa [prefixWord, tailWord_2374340, baseEnd_2374340] using wordTrace_append hprefix tailTrace_2374340
  have hstable : (prefixWord ++ tailWord_2374340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374340).length < 2 ^ (prefixWord ++ tailWord_2374340).sum := by decide
  have hdescent : baseEnd_2374340 < baseStart_2374340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374367 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2374367 : Nat := 118140960795 + 2374367 * 2 ^ 59
def prefixEnd_2374367 : Nat := 4983230072969 + 3 ^ 40 * 2374367 * 2
def baseEnd_2374367 : Nat := 1219191521174017011892991

theorem tailTrace_2374367 : CollatzResearch.WordTrace tailWord_2374367 prefixEnd_2374367 1219191521174017011892991 := by
  unfold tailWord_2374367
  simp only [CollatzResearch.WordTrace]
  refine ⟨86600278989081343444441355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57733519326054228962960903 86600278989081343444441355)
  ·
    refine ⟨129900418483622015166662033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86600278989081343444441355 129900418483622015166662033)
    ·
      refine ⟨97425313862716511374996525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129900418483622015166662033 97425313862716511374996525)
      ·
        refine ⟨36534492698518691765623697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97425313862716511374996525 36534492698518691765623697)
        ·
          refine ⟨27400869523889018824217773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36534492698518691765623697 27400869523889018824217773)
          ·
            refine ⟨10275326071458382059081665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27400869523889018824217773 10275326071458382059081665)
            ·
              refine ⟨7706494553593786544311249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10275326071458382059081665 7706494553593786544311249)
              ·
                refine ⟨5779870915195339908233437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7706494553593786544311249 5779870915195339908233437)
                ·
                  refine ⟨2167451593198252465587539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5779870915195339908233437 2167451593198252465587539)
                  ·
                    refine ⟨3251177389797378698381309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2167451593198252465587539 3251177389797378698381309)
                    ·
                      refine ⟨1219191521174017011892991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251177389797378698381309 1219191521174017011892991)
                      ·
                        rfl

theorem cell23_2374367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2374367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374367 prefixEnd_2374367 := by exact prefixLift 2374367
  have htrace : WordTrace (prefixWord ++ tailWord_2374367) baseStart_2374367 baseEnd_2374367 := by
    simpa [prefixWord, tailWord_2374367, baseEnd_2374367] using wordTrace_append hprefix tailTrace_2374367
  have hstable : (prefixWord ++ tailWord_2374367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374367).length < 2 ^ (prefixWord ++ tailWord_2374367).sum := by decide
  have hdescent : baseEnd_2374367 < baseStart_2374367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374410 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2374410 : Nat := 118140960795 + 2374410 * 2 ^ 59
def prefixEnd_2374410 : Nat := 4983230072969 + 3 ^ 40 * 2374410 * 2
def baseEnd_2374410 : Nat := 1219213600842160343655293

theorem tailTrace_2374410 : CollatzResearch.WordTrace tailWord_2374410 prefixEnd_2374410 1219213600842160343655293 := by
  unfold tailWord_2374410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650461831981390447064171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57734564885283707858837789 21650461831981390447064171)
  ·
    refine ⟨32475692747972085670596257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21650461831981390447064171 32475692747972085670596257)
    ·
      refine ⟨24356769560979064252947193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32475692747972085670596257 24356769560979064252947193)
      ·
        refine ⟨18267577170734298189710395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24356769560979064252947193 18267577170734298189710395)
        ·
          refine ⟨27401365756101447284565593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18267577170734298189710395 27401365756101447284565593)
          ·
            refine ⟨20551024317076085463424195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27401365756101447284565593 20551024317076085463424195)
            ·
              refine ⟨30826536475614128195136293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20551024317076085463424195 30826536475614128195136293)
              ·
                refine ⟨5779975589177649036588055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30826536475614128195136293 5779975589177649036588055)
                ·
                  refine ⟨8669963383766473554882083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779975589177649036588055 8669963383766473554882083)
                  ·
                    refine ⟨13004945075649710332323125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8669963383766473554882083 13004945075649710332323125)
                    ·
                      refine ⟨1219213600842160343655293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13004945075649710332323125 1219213600842160343655293)
                      ·
                        rfl

theorem cell23_2374410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2374410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374410 prefixEnd_2374410 := by exact prefixLift 2374410
  have htrace : WordTrace (prefixWord ++ tailWord_2374410) baseStart_2374410 baseEnd_2374410 := by
    simpa [prefixWord, tailWord_2374410, baseEnd_2374410] using wordTrace_append hprefix tailTrace_2374410
  have hstable : (prefixWord ++ tailWord_2374410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374410).length < 2 ^ (prefixWord ++ tailWord_2374410).sum := by decide
  have hdescent : baseEnd_2374410 < baseStart_2374410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374443 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 9]
def baseStart_2374443 : Nat := 118140960795 + 2374443 * 2 ^ 59
def prefixEnd_2374443 : Nat := 4983230072969 + 3 ^ 40 * 2374443 * 2
def baseEnd_2374443 : Nat := 406410181901252904847547

theorem tailTrace_2374443 : CollatzResearch.WordTrace tailWord_2374443 prefixEnd_2374443 406410181901252904847547 := by
  unfold tailWord_2374443
  simp only [CollatzResearch.WordTrace]
  refine ⟨86603050936806008424207983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57735367291204005616138655 86603050936806008424207983)
  ·
    refine ⟨129904576405209012636311975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86603050936806008424207983 129904576405209012636311975)
    ·
      refine ⟨194856864607813518954467963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129904576405209012636311975 194856864607813518954467963)
      ·
        refine ⟨292285296911720278431701945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194856864607813518954467963 292285296911720278431701945)
        ·
          refine ⟨219213972683790208823776459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292285296911720278431701945 219213972683790208823776459)
          ·
            refine ⟨328820959025685313235664689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219213972683790208823776459 328820959025685313235664689)
            ·
              refine ⟨246615719269263984926748517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328820959025685313235664689 246615719269263984926748517)
              ·
                refine ⟨46240447362986997173765347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246615719269263984926748517 46240447362986997173765347)
                ·
                  refine ⟨69360671044480495760648021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46240447362986997173765347 69360671044480495760648021)
                  ·
                    refine ⟨406410181901252904847547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69360671044480495760648021 406410181901252904847547)
                    ·
                      rfl

theorem cell23_2374443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_2374443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374443 prefixEnd_2374443 := by exact prefixLift 2374443
  have htrace : WordTrace (prefixWord ++ tailWord_2374443) baseStart_2374443 baseEnd_2374443 := by
    simpa [prefixWord, tailWord_2374443, baseEnd_2374443] using wordTrace_append hprefix tailTrace_2374443
  have hstable : (prefixWord ++ tailWord_2374443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374443).length < 2 ^ (prefixWord ++ tailWord_2374443).sum := by decide
  have hdescent : baseEnd_2374443 < baseStart_2374443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374444 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_2374444 : Nat := 118140960795 + 2374444 * 2 ^ 59
def prefixEnd_2374444 : Nat := 4983230072969 + 3 ^ 40 * 2374444 * 2
def baseEnd_2374444 : Nat := 1219231059184413210630137

theorem tailTrace_2374444 : CollatzResearch.WordTrace tailWord_2374444 prefixEnd_2374444 1219231059184413210630137 := by
  unfold tailWord_2374444
  simp only [CollatzResearch.WordTrace]
  refine ⟨43301543704901192797497193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57735391606534923729996257 43301543704901192797497193)
  ·
    refine ⟨32476157778675894598122895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43301543704901192797497193 32476157778675894598122895)
    ·
      refine ⟨48714236668013841897184343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476157778675894598122895 48714236668013841897184343)
      ·
        refine ⟨73071355002020762845776515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48714236668013841897184343 73071355002020762845776515)
        ·
          refine ⟨109607032503031144268664773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73071355002020762845776515 109607032503031144268664773)
          ·
            refine ⟨20551318594318339550374645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109607032503031144268664773 20551318594318339550374645)
            ·
              refine ⟨1926686118217344332847623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20551318594318339550374645 1926686118217344332847623)
              ·
                refine ⟨2890029177326016499271435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926686118217344332847623 2890029177326016499271435)
                ·
                  refine ⟨4335043765989024748907153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890029177326016499271435 4335043765989024748907153)
                  ·
                    refine ⟨3251282824491768561680365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335043765989024748907153 3251282824491768561680365)
                    ·
                      refine ⟨1219231059184413210630137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251282824491768561680365 1219231059184413210630137)
                      ·
                        rfl

theorem cell23_2374444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_2374444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374444 prefixEnd_2374444 := by exact prefixLift 2374444
  have htrace : WordTrace (prefixWord ++ tailWord_2374444) baseStart_2374444 baseEnd_2374444 := by
    simpa [prefixWord, tailWord_2374444, baseEnd_2374444] using wordTrace_append hprefix tailTrace_2374444
  have hstable : (prefixWord ++ tailWord_2374444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374444).length < 2 ^ (prefixWord ++ tailWord_2374444).sum := by decide
  have hdescent : baseEnd_2374444 < baseStart_2374444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374452 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2374452 : Nat := 118140960795 + 2374452 * 2 ^ 59
def prefixEnd_2374452 : Nat := 4983230072969 + 3 ^ 40 * 2374452 * 2
def baseEnd_2374452 : Nat := 1219235167029649179330101

theorem tailTrace_2374452 : CollatzResearch.WordTrace tailWord_2374452 prefixEnd_2374452 1219235167029649179330101 := by
  unfold tailWord_2374452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43301689596886701480642805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57735586129182268640857073 43301689596886701480642805)
  ·
    refine ⟨4059533399708128263810263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43301689596886701480642805 4059533399708128263810263)
    ·
      refine ⟨6089300099562192395715395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059533399708128263810263 6089300099562192395715395)
      ·
        refine ⟨9133950149343288593573093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6089300099562192395715395 9133950149343288593573093)
        ·
          refine ⟨1712615653001866611294955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9133950149343288593573093 1712615653001866611294955)
          ·
            refine ⟨2568923479502799916942433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712615653001866611294955 2568923479502799916942433)
            ·
              refine ⟨1926692609627099937706825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568923479502799916942433 1926692609627099937706825)
              ·
                refine ⟨1445019457220324953280119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926692609627099937706825 1445019457220324953280119)
                ·
                  refine ⟨2167529185830487429920179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445019457220324953280119 2167529185830487429920179)
                  ·
                    refine ⟨3251293778745731144880269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2167529185830487429920179 3251293778745731144880269)
                    ·
                      refine ⟨1219235167029649179330101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251293778745731144880269 1219235167029649179330101)
                      ·
                        rfl

theorem cell23_2374452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2374452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374452 prefixEnd_2374452 := by exact prefixLift 2374452
  have htrace : WordTrace (prefixWord ++ tailWord_2374452) baseStart_2374452 baseEnd_2374452 := by
    simpa [prefixWord, tailWord_2374452, baseEnd_2374452] using wordTrace_append hprefix tailTrace_2374452
  have hstable : (prefixWord ++ tailWord_2374452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374452).length < 2 ^ (prefixWord ++ tailWord_2374452).sum := by decide
  have hdescent : baseEnd_2374452 < baseStart_2374452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374458 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_2374458 : Nat := 118140960795 + 2374458 * 2 ^ 59
def prefixEnd_2374458 : Nat := 4983230072969 + 3 ^ 40 * 2374458 * 2
def baseEnd_2374458 : Nat := 1219238247913576155855073

theorem tailTrace_2374458 : CollatzResearch.WordTrace tailWord_2374458 prefixEnd_2374458 1219238247913576155855073 := by
  unfold tailWord_2374458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650899507937916496501007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57735732021167777324002685 21650899507937916496501007)
  ·
    refine ⟨32476349261906874744751511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21650899507937916496501007 32476349261906874744751511)
    ·
      refine ⟨48714523892860312117127267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476349261906874744751511 48714523892860312117127267)
      ·
        refine ⟨73071785839290468175690901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48714523892860312117127267 73071785839290468175690901)
        ·
          refine ⟨3425239961216740695735511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73071785839290468175690901 3425239961216740695735511)
          ·
            refine ⟨5137859941825111043603267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425239961216740695735511 5137859941825111043603267)
            ·
              refine ⟨7706789912737666565404901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137859941825111043603267 7706789912737666565404901)
              ·
                refine ⟨1445023108638312481013419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7706789912737666565404901 1445023108638312481013419)
                ·
                  refine ⟨2167534662957468721520129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445023108638312481013419 2167534662957468721520129)
                  ·
                    refine ⟨1625650997218101541140097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2167534662957468721520129 1625650997218101541140097)
                    ·
                      refine ⟨1219238247913576155855073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625650997218101541140097 1219238247913576155855073)
                      ·
                        rfl

theorem cell23_2374458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_2374458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374458 prefixEnd_2374458 := by exact prefixLift 2374458
  have htrace : WordTrace (prefixWord ++ tailWord_2374458) baseStart_2374458 baseEnd_2374458 := by
    simpa [prefixWord, tailWord_2374458, baseEnd_2374458] using wordTrace_append hprefix tailTrace_2374458
  have hstable : (prefixWord ++ tailWord_2374458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374458).length < 2 ^ (prefixWord ++ tailWord_2374458).sum := by decide
  have hdescent : baseEnd_2374458 < baseStart_2374458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374467 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 5, 3, 2]
def baseStart_2374467 : Nat := 118140960795 + 2374467 * 2 ^ 59
def prefixEnd_2374467 : Nat := 4983230072969 + 3 ^ 40 * 2374467 * 2
def baseEnd_2374467 : Nat := 1219242869239466620642531

theorem tailTrace_2374467 : CollatzResearch.WordTrace tailWord_2374467 prefixEnd_2374467 1219242869239466620642531 := by
  unfold tailWord_2374467
  simp only [CollatzResearch.WordTrace]
  refine ⟨86603926288719060523081655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57735950859146040348721103 86603926288719060523081655)
  ·
    refine ⟨129905889433078590784622483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86603926288719060523081655 129905889433078590784622483)
    ·
      refine ⟨194858834149617886176933725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129905889433078590784622483 194858834149617886176933725)
      ·
        refine ⟨73072062806106707316350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194858834149617886176933725 73072062806106707316350147)
        ·
          refine ⟨109608094209160060974525221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73072062806106707316350147 109608094209160060974525221)
          ·
            refine ⟨20551517664217511432723479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109608094209160060974525221 20551517664217511432723479)
            ·
              refine ⟨30827276496326267149085219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20551517664217511432723479 30827276496326267149085219)
              ·
                refine ⟨46240914744489400723627829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30827276496326267149085219 46240914744489400723627829)
                ·
                  refine ⟨4335085757295881317840109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46240914744489400723627829 4335085757295881317840109)
                  ·
                    refine ⟨1625657158985955494190041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4335085757295881317840109 1625657158985955494190041)
                    ·
                      refine ⟨1219242869239466620642531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625657158985955494190041 1219242869239466620642531)
                      ·
                        rfl

theorem cell23_2374467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_2374467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374467 prefixEnd_2374467 := by exact prefixLift 2374467
  have htrace : WordTrace (prefixWord ++ tailWord_2374467) baseStart_2374467 baseEnd_2374467 := by
    simpa [prefixWord, tailWord_2374467, baseEnd_2374467] using wordTrace_append hprefix tailTrace_2374467
  have hstable : (prefixWord ++ tailWord_2374467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374467).length < 2 ^ (prefixWord ++ tailWord_2374467).sum := by decide
  have hdescent : baseEnd_2374467 < baseStart_2374467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_2374497 : Nat := 118140960795 + 2374497 * 2 ^ 59
def prefixEnd_2374497 : Nat := 4983230072969 + 3 ^ 40 * 2374497 * 2
def baseEnd_2374497 : Nat := 1219258273659101503267393

theorem tailTrace_2374497 : CollatzResearch.WordTrace tailWord_2374497 prefixEnd_2374497 1219258273659101503267393 := by
  unfold tailWord_2374497
  simp only [CollatzResearch.WordTrace]
  refine ⟨86605020478610375646673745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57736680319073583764449163 86605020478610375646673745)
  ·
    refine ⟨64953765358957781735005309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86605020478610375646673745 64953765358957781735005309)
    ·
      refine ⟨24357662009609168150626991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64953765358957781735005309 24357662009609168150626991)
      ·
        refine ⟨36536493014413752225940487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24357662009609168150626991 36536493014413752225940487)
        ·
          refine ⟨54804739521620628338910731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36536493014413752225940487 54804739521620628338910731)
          ·
            refine ⟨82207109282430942508366097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54804739521620628338910731 82207109282430942508366097)
            ·
              refine ⟨61655331961823206881274573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82207109282430942508366097 61655331961823206881274573)
              ·
                refine ⟨23120749485683702580477965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61655331961823206881274573 23120749485683702580477965)
                ·
                  refine ⟨8670281057131388467679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23120749485683702580477965 8670281057131388467679237)
                  ·
                    refine ⟨1625677698212135337689857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8670281057131388467679237 1625677698212135337689857)
                    ·
                      refine ⟨1219258273659101503267393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625677698212135337689857 1219258273659101503267393)
                      ·
                        rfl

theorem cell23_2374497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_2374497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374497 prefixEnd_2374497 := by exact prefixLift 2374497
  have htrace : WordTrace (prefixWord ++ tailWord_2374497) baseStart_2374497 baseEnd_2374497 := by
    simpa [prefixWord, tailWord_2374497, baseEnd_2374497] using wordTrace_append hprefix tailTrace_2374497
  have hstable : (prefixWord ++ tailWord_2374497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374497).length < 2 ^ (prefixWord ++ tailWord_2374497).sum := by decide
  have hdescent : baseEnd_2374497 < baseStart_2374497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374501 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_2374501 : Nat := 118140960795 + 2374501 * 2 ^ 59
def prefixEnd_2374501 : Nat := 4983230072969 + 3 ^ 40 * 2374501 * 2
def baseEnd_2374501 : Nat := 1219260327581719487617375

theorem tailTrace_2374501 : CollatzResearch.WordTrace tailWord_2374501 prefixEnd_2374501 1219260327581719487617375 := by
  unfold tailWord_2374501
  simp only [CollatzResearch.WordTrace]
  refine ⟨86605166370595884329819357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57736777580397256219879571 86605166370595884329819357)
  ·
    refine ⟨32476937388973456623682259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86605166370595884329819357 32476937388973456623682259)
    ·
      refine ⟨48715406083460184935523389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476937388973456623682259 48715406083460184935523389)
      ·
        refine ⟨18268277281297569350821271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48715406083460184935523389 18268277281297569350821271)
        ·
          refine ⟨27402415921946354026231907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18268277281297569350821271 27402415921946354026231907)
          ·
            refine ⟨41103623882919531039347861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27402415921946354026231907 41103623882919531039347861)
            ·
              refine ⟨1926732369511853017469431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41103623882919531039347861 1926732369511853017469431)
              ·
                refine ⟨2890098554267779526204147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926732369511853017469431 2890098554267779526204147)
                ·
                  refine ⟨4335147831401669289306221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890098554267779526204147 4335147831401669289306221)
                  ·
                    refine ⟨1625680436775625983489833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4335147831401669289306221 1625680436775625983489833)
                    ·
                      refine ⟨1219260327581719487617375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1625680436775625983489833 1219260327581719487617375)
                      ·
                        rfl

theorem cell23_2374501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_2374501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374501 prefixEnd_2374501 := by exact prefixLift 2374501
  have htrace : WordTrace (prefixWord ++ tailWord_2374501) baseStart_2374501 baseEnd_2374501 := by
    simpa [prefixWord, tailWord_2374501, baseEnd_2374501] using wordTrace_append hprefix tailTrace_2374501
  have hstable : (prefixWord ++ tailWord_2374501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374501).length < 2 ^ (prefixWord ++ tailWord_2374501).sum := by decide
  have hdescent : baseEnd_2374501 < baseStart_2374501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374604 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2374604 : Nat := 118140960795 + 2374604 * 2 ^ 59
def prefixEnd_2374604 : Nat := 4983230072969 + 3 ^ 40 * 2374604 * 2
def baseEnd_2374604 : Nat := 1219313216089132584629401

theorem tailTrace_2374604 : CollatzResearch.WordTrace tailWord_2374604 prefixEnd_2374604 1219313216089132584629401 := by
  unfold tailWord_2374604
  simp only [CollatzResearch.WordTrace]
  refine ⟨43304461544611366460409433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57739282059481821947212577 43304461544611366460409433)
  ·
    refine ⟨32478346158458524845307075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43304461544611366460409433 32478346158458524845307075)
    ·
      refine ⟨48717519237687787267960613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32478346158458524845307075 48717519237687787267960613)
      ·
        refine ⟨9134534857066460112742615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48717519237687787267960613 9134534857066460112742615)
        ·
          refine ⟨13701802285599690169113923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9134534857066460112742615 13701802285599690169113923)
          ·
            refine ⟨20552703428399535253670885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701802285599690169113923 20552703428399535253670885)
            ·
              refine ⟨3853631892824912860063291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20552703428399535253670885 3853631892824912860063291)
              ·
                refine ⟨5780447839237369290094937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853631892824912860063291 5780447839237369290094937)
                ·
                  refine ⟨4335335879428026967571203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780447839237369290094937 4335335879428026967571203)
                  ·
                    refine ⟨6503003819142040451356805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335335879428026967571203 6503003819142040451356805)
                    ·
                      refine ⟨1219313216089132584629401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6503003819142040451356805 1219313216089132584629401)
                      ·
                        rfl

theorem cell23_2374604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2374604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374604 prefixEnd_2374604 := by exact prefixLift 2374604
  have htrace : WordTrace (prefixWord ++ tailWord_2374604) baseStart_2374604 baseEnd_2374604 := by
    simpa [prefixWord, tailWord_2374604, baseEnd_2374604] using wordTrace_append hprefix tailTrace_2374604
  have hstable : (prefixWord ++ tailWord_2374604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374604).length < 2 ^ (prefixWord ++ tailWord_2374604).sum := by decide
  have hdescent : baseEnd_2374604 < baseStart_2374604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374658 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2374658 : Nat := 118140960795 + 2374658 * 2 ^ 59
def prefixEnd_2374658 : Nat := 4983230072969 + 3 ^ 40 * 2374658 * 2
def baseEnd_2374658 : Nat := 1219340944044475373354153

theorem tailTrace_2374658 : CollatzResearch.WordTrace tailWord_2374658 prefixEnd_2374658 1219340944044475373354153 := by
  unfold tailWord_2374658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21652723157756775035821157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57740595087351400095523085 21652723157756775035821157)
  ·
    refine ⟨4059885592079395319216467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21652723157756775035821157 4059885592079395319216467)
    ·
      refine ⟨6089828388119092978824701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059885592079395319216467 6089828388119092978824701)
      ·
        refine ⟨2283685645544659867059263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6089828388119092978824701 2283685645544659867059263)
        ·
          refine ⟨3425528468316989800588895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283685645544659867059263 3425528468316989800588895)
          ·
            refine ⟨5138292702475484700883343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425528468316989800588895 5138292702475484700883343)
            ·
              refine ⟨7707439053713227051325015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138292702475484700883343 7707439053713227051325015)
              ·
                refine ⟨11561158580569840576987523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707439053713227051325015 11561158580569840576987523)
                ·
                  refine ⟨17341737870854760865481285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11561158580569840576987523 17341737870854760865481285)
                  ·
                    refine ⟨3251575850785267662277741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17341737870854760865481285 3251575850785267662277741)
                    ·
                      refine ⟨1219340944044475373354153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251575850785267662277741 1219340944044475373354153)
                      ·
                        rfl

theorem cell23_2374658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2374658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374658 prefixEnd_2374658 := by exact prefixLift 2374658
  have htrace : WordTrace (prefixWord ++ tailWord_2374658) baseStart_2374658 baseEnd_2374658 := by
    simpa [prefixWord, tailWord_2374658, baseEnd_2374658] using wordTrace_append hprefix tailTrace_2374658
  have hstable : (prefixWord ++ tailWord_2374658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374658).length < 2 ^ (prefixWord ++ tailWord_2374658).sum := by decide
  have hdescent : baseEnd_2374658 < baseStart_2374658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374708 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2374708 : Nat := 118140960795 + 2374708 * 2 ^ 59
def prefixEnd_2374708 : Nat := 4983230072969 + 3 ^ 40 * 2374708 * 2
def baseEnd_2374708 : Nat := 406455539359066725909641

theorem tailTrace_2374708 : CollatzResearch.WordTrace tailWord_2374708 prefixEnd_2374708 406455539359066725909641 := by
  unfold tailWord_2374708
  simp only [CollatzResearch.WordTrace]
  refine ⟨43306358140422979341302389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57741810853897305788403185 43306358140422979341302389)
  ·
    refine ⟨4059971075664654313247099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43306358140422979341302389 4059971075664654313247099)
    ·
      refine ⟨6089956613496981469870649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059971075664654313247099 6089956613496981469870649)
      ·
        refine ⟨4567467460122736102402987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089956613496981469870649 4567467460122736102402987)
        ·
          refine ⟨6851201190184104153604481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567467460122736102402987 6851201190184104153604481)
          ·
            refine ⟨5138400892638078115203361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6851201190184104153604481 5138400892638078115203361)
            ·
              refine ⟨3853800669478558586402521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138400892638078115203361 3853800669478558586402521)
              ·
                refine ⟨2890350502108918939801891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3853800669478558586402521 2890350502108918939801891)
                ·
                  refine ⟨4335525753163378409702837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890350502108918939801891 4335525753163378409702837)
                  ·
                    refine ⟨406455539359066725909641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4335525753163378409702837 406455539359066725909641)
                    ·
                      rfl

theorem cell23_2374708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2374708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374708 prefixEnd_2374708 := by exact prefixLift 2374708
  have htrace : WordTrace (prefixWord ++ tailWord_2374708) baseStart_2374708 baseEnd_2374708 := by
    simpa [prefixWord, tailWord_2374708, baseEnd_2374708] using wordTrace_append hprefix tailTrace_2374708
  have hstable : (prefixWord ++ tailWord_2374708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374708).length < 2 ^ (prefixWord ++ tailWord_2374708).sum := by decide
  have hdescent : baseEnd_2374708 < baseStart_2374708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374714 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_2374714 : Nat := 118140960795 + 2374714 * 2 ^ 59
def prefixEnd_2374714 : Nat := 4983230072969 + 3 ^ 40 * 2374714 * 2
def baseEnd_2374714 : Nat := 1219369698961127154253895

theorem tailTrace_2374714 : CollatzResearch.WordTrace tailWord_2374714 prefixEnd_2374714 1219369698961127154253895 := by
  unfold tailWord_2374714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653233779706055426830799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57741956745882814471548797 21653233779706055426830799)
  ·
    refine ⟨32479850669559083140246199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653233779706055426830799 32479850669559083140246199)
    ·
      refine ⟨48719776004338624710369299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32479850669559083140246199 48719776004338624710369299)
      ·
        refine ⟨73079664006507937065553949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48719776004338624710369299 73079664006507937065553949)
        ·
          refine ⟨27404874002440476399582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73079664006507937065553949 27404874002440476399582731)
          ·
            refine ⟨41107311003660714599374097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27404874002440476399582731 41107311003660714599374097)
            ·
              refine ⟨30830483252745535949530573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41107311003660714599374097 30830483252745535949530573)
              ·
                refine ⟨11561431219779575981073965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30830483252745535949530573 11561431219779575981073965)
                ·
                  refine ⟨4335536707417340992902737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561431219779575981073965 4335536707417340992902737)
                  ·
                    refine ⟨3251652530563005744677053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335536707417340992902737 3251652530563005744677053)
                    ·
                      refine ⟨1219369698961127154253895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251652530563005744677053 1219369698961127154253895)
                      ·
                        rfl

theorem cell23_2374714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_2374714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374714 prefixEnd_2374714 := by exact prefixLift 2374714
  have htrace : WordTrace (prefixWord ++ tailWord_2374714) baseStart_2374714 baseEnd_2374714 := by
    simpa [prefixWord, tailWord_2374714, baseEnd_2374714] using wordTrace_append hprefix tailTrace_2374714
  have hstable : (prefixWord ++ tailWord_2374714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374714).length < 2 ^ (prefixWord ++ tailWord_2374714).sum := by decide
  have hdescent : baseEnd_2374714 < baseStart_2374714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374782 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2374782 : Nat := 118140960795 + 2374782 * 2 ^ 59
def prefixEnd_2374782 : Nat := 4983230072969 + 3 ^ 40 * 2374782 * 2
def baseEnd_2374782 : Nat := 1219404615645632888203583

theorem tailTrace_2374782 : CollatzResearch.WordTrace tailWord_2374782 prefixEnd_2374782 1219404615645632888203583 := by
  unfold tailWord_2374782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826926910322233665099825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57743610188385246213865733 10826926910322233665099825)
  ·
    refine ⟨8120195182741675248824869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10826926910322233665099825 8120195182741675248824869)
    ·
      refine ⟨1522536596764064109154663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8120195182741675248824869 1522536596764064109154663)
      ·
        refine ⟨2283804895146096163731995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522536596764064109154663 2283804895146096163731995)
        ·
          refine ⟨3425707342719144245597993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283804895146096163731995 3425707342719144245597993)
          ·
            refine ⟨2569280507039358184198495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425707342719144245597993 2569280507039358184198495)
            ·
              refine ⟨3853920760559037276297743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569280507039358184198495 3853920760559037276297743)
              ·
                refine ⟨5780881140838555914446615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853920760559037276297743 5780881140838555914446615)
                ·
                  refine ⟨8671321711257833871669923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780881140838555914446615 8671321711257833871669923)
                  ·
                    refine ⟨13006982566886750807504885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8671321711257833871669923 13006982566886750807504885)
                    ·
                      refine ⟨1219404615645632888203583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13006982566886750807504885 1219404615645632888203583)
                      ·
                        rfl

theorem cell23_2374782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2374782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374782 prefixEnd_2374782 := by exact prefixLift 2374782
  have htrace : WordTrace (prefixWord ++ tailWord_2374782) baseStart_2374782 baseEnd_2374782 := by
    simpa [prefixWord, tailWord_2374782, baseEnd_2374782] using wordTrace_append hprefix tailTrace_2374782
  have hstable : (prefixWord ++ tailWord_2374782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374782).length < 2 ^ (prefixWord ++ tailWord_2374782).sum := by decide
  have hdescent : baseEnd_2374782 < baseStart_2374782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374794 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_2374794 : Nat := 118140960795 + 2374794 * 2 ^ 59
def prefixEnd_2374794 : Nat := 4983230072969 + 3 ^ 40 * 2374794 * 2
def baseEnd_2374794 : Nat := 406470259137828947084509

theorem tailTrace_2374794 : CollatzResearch.WordTrace tailWord_2374794 prefixEnd_2374794 406470259137828947084509 := by
  unfold tailWord_2374794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653963239633598842558859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57743901972356263580156957 21653963239633598842558859)
  ·
    refine ⟨32480944859450398263838289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653963239633598842558859 32480944859450398263838289)
    ·
      refine ⟨24360708644587798697878717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32480944859450398263838289 24360708644587798697878717)
      ·
        refine ⟨9135265741720424511704519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24360708644587798697878717 9135265741720424511704519)
        ·
          refine ⟨13702898612580636767556779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9135265741720424511704519 13702898612580636767556779)
          ·
            refine ⟨20554347918870955151335169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13702898612580636767556779 20554347918870955151335169)
            ·
              refine ⟨15415760939153216363501377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20554347918870955151335169 15415760939153216363501377)
              ·
                refine ⟨11561820704364912272626033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15415760939153216363501377 11561820704364912272626033)
                ·
                  refine ⟨8671365528273684204469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11561820704364912272626033 8671365528273684204469525)
                  ·
                    refine ⟨406470259137828947084509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8671365528273684204469525 406470259137828947084509)
                    ·
                      rfl

theorem cell23_2374794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_2374794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374794 prefixEnd_2374794 := by exact prefixLift 2374794
  have htrace : WordTrace (prefixWord ++ tailWord_2374794) baseStart_2374794 baseEnd_2374794 := by
    simpa [prefixWord, tailWord_2374794, baseEnd_2374794] using wordTrace_append hprefix tailTrace_2374794
  have hstable : (prefixWord ++ tailWord_2374794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374794).length < 2 ^ (prefixWord ++ tailWord_2374794).sum := by decide
  have hdescent : baseEnd_2374794 < baseStart_2374794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374841 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 5]
def baseStart_2374841 : Nat := 118140960795 + 2374841 * 2 ^ 59
def prefixEnd_2374841 : Nat := 4983230072969 + 3 ^ 40 * 2374841 * 2
def baseEnd_2374841 : Nat := 135492767889360906373979

theorem tailTrace_2374841 : CollatzResearch.WordTrace tailWord_2374841 prefixEnd_2374841 135492767889360906373979 := by
  unfold tailWord_2374841
  simp only [CollatzResearch.WordTrace]
  refine ⟨86617567189364122397196377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57745044792909414931464251 86617567189364122397196377)
  ·
    refine ⟨64963175392023091797897283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86617567189364122397196377 64963175392023091797897283)
    ·
      refine ⟨97444763088034637696845925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64963175392023091797897283 97444763088034637696845925)
      ·
        refine ⟨18270893079006494568158611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97444763088034637696845925 18270893079006494568158611)
        ·
          refine ⟨27406339618509741852237917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18270893079006494568158611 27406339618509741852237917)
          ·
            refine ⟨10277377356941153194589219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27406339618509741852237917 10277377356941153194589219)
            ·
              refine ⟨15416066035411729791883829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277377356941153194589219 15416066035411729791883829)
              ·
                refine ⟨1445256190819849667989109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15416066035411729791883829 1445256190819849667989109)
                ·
                  refine ⟨135492767889360906373979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1445256190819849667989109 135492767889360906373979)
                  ·
                    rfl

theorem cell23_2374841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 5].length) (baseStart_2374841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374841 prefixEnd_2374841 := by exact prefixLift 2374841
  have htrace : WordTrace (prefixWord ++ tailWord_2374841) baseStart_2374841 baseEnd_2374841 := by
    simpa [prefixWord, tailWord_2374841, baseEnd_2374841] using wordTrace_append hprefix tailTrace_2374841
  have hstable : (prefixWord ++ tailWord_2374841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374841).length < 2 ^ (prefixWord ++ tailWord_2374841).sum := by decide
  have hdescent : baseEnd_2374841 < baseStart_2374841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374908 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_2374908 : Nat := 118140960795 + 2374908 * 2 ^ 59
def prefixEnd_2374908 : Nat := 4983230072969 + 3 ^ 40 * 2374908 * 2
def baseEnd_2374908 : Nat := 1219469314208099395228003

theorem tailTrace_2374908 : CollatzResearch.WordTrace tailWord_2374908 prefixEnd_2374908 1219469314208099395228003 := by
  unfold tailWord_2374908
  simp only [CollatzResearch.WordTrace]
  refine ⟨43310005440060696419942689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57746673920080928559923585 43310005440060696419942689)
  ·
    refine ⟨32482504080045522314957017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43310005440060696419942689 32482504080045522314957017)
    ·
      refine ⟨24361878060034141736217763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32482504080045522314957017 24361878060034141736217763)
      ·
        refine ⟨36542817090051212604326645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24361878060034141736217763 36542817090051212604326645)
        ·
          refine ⟨3425889102192301181655623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36542817090051212604326645 3425889102192301181655623)
          ·
            refine ⟨5138833653288451772483435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425889102192301181655623 5138833653288451772483435)
            ·
              refine ⟨7708250479932677658725153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138833653288451772483435 7708250479932677658725153)
              ·
                refine ⟨5781187859949508244043865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7708250479932677658725153 5781187859949508244043865)
                ·
                  refine ⟨4335890894962131183032899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781187859949508244043865 4335890894962131183032899)
                  ·
                    refine ⟨6503836342443196774549349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335890894962131183032899 6503836342443196774549349)
                    ·
                      refine ⟨1219469314208099395228003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6503836342443196774549349 1219469314208099395228003)
                      ·
                        rfl

theorem cell23_2374908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_2374908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374908 prefixEnd_2374908 := by exact prefixLift 2374908
  have htrace : WordTrace (prefixWord ++ tailWord_2374908) baseStart_2374908 baseEnd_2374908 := by
    simpa [prefixWord, tailWord_2374908, baseEnd_2374908] using wordTrace_append hprefix tailTrace_2374908
  have hstable : (prefixWord ++ tailWord_2374908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374908).length < 2 ^ (prefixWord ++ tailWord_2374908).sum := by decide
  have hdescent : baseEnd_2374908 < baseStart_2374908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374911 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_2374911 : Nat := 118140960795 + 2374911 * 2 ^ 59
def prefixEnd_2374911 : Nat := 4983230072969 + 3 ^ 40 * 2374911 * 2
def baseEnd_2374911 : Nat := 1219470854650062883490489

theorem tailTrace_2374911 : CollatzResearch.WordTrace tailWord_2374911 prefixEnd_2374911 1219470854650062883490489 := by
  unfold tailWord_2374911
  simp only [CollatzResearch.WordTrace]
  refine ⟨86620120299110524352244587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57746746866073682901496391 86620120299110524352244587)
  ·
    refine ⟨129930180448665786528366881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86620120299110524352244587 129930180448665786528366881)
    ·
      refine ⟨97447635336499339896275161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129930180448665786528366881 97447635336499339896275161)
      ·
        refine ⟨73085726502374504922206371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97447635336499339896275161 73085726502374504922206371)
        ·
          refine ⟨109628589753561757383309557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73085726502374504922206371 109628589753561757383309557)
          ·
            refine ⟨10277680289396414754685271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109628589753561757383309557 10277680289396414754685271)
            ·
              refine ⟨15416520434094622132027907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277680289396414754685271 15416520434094622132027907)
              ·
                refine ⟨23124780651141933198041861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15416520434094622132027907 23124780651141933198041861)
                ·
                  refine ⟨4335896372089112474632849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23124780651141933198041861 4335896372089112474632849)
                  ·
                    refine ⟨3251922279066834355974637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335896372089112474632849 3251922279066834355974637)
                    ·
                      refine ⟨1219470854650062883490489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3251922279066834355974637 1219470854650062883490489)
                      ·
                        rfl

theorem cell23_2374911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_2374911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374911 prefixEnd_2374911 := by exact prefixLift 2374911
  have htrace : WordTrace (prefixWord ++ tailWord_2374911) baseStart_2374911 baseEnd_2374911 := by
    simpa [prefixWord, tailWord_2374911, baseEnd_2374911] using wordTrace_append hprefix tailTrace_2374911
  have hstable : (prefixWord ++ tailWord_2374911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374911).length < 2 ^ (prefixWord ++ tailWord_2374911).sum := by decide
  have hdescent : baseEnd_2374911 < baseStart_2374911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374942 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2374942 : Nat := 118140960795 + 2374942 * 2 ^ 59
def prefixEnd_2374942 : Nat := 4983230072969 + 3 ^ 40 * 2374942 * 2
def baseEnd_2374942 : Nat := 1219486772550352262202847

theorem tailTrace_2374942 : CollatzResearch.WordTrace tailWord_2374942 prefixEnd_2374942 1219486772550352262202847 := by
  unfold tailWord_2374942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827656370249777080827885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57747500641332144431082053 10827656370249777080827885)
  ·
    refine ⟨4060371138843666405310457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10827656370249777080827885 4060371138843666405310457)
    ·
      refine ⟨3045278354132749803982843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060371138843666405310457 3045278354132749803982843)
      ·
        refine ⟨4567917531199124705974265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045278354132749803982843 4567917531199124705974265)
        ·
          refine ⟨3425938148399343529480699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567917531199124705974265 3425938148399343529480699)
          ·
            refine ⟨5138907222599015294221049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425938148399343529480699 5138907222599015294221049)
            ·
              refine ⟨3854180416949261470665787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138907222599015294221049 3854180416949261470665787)
              ·
                refine ⟨5781270625423892205998681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854180416949261470665787 5781270625423892205998681)
                ·
                  refine ⟨4335952969067919154499011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781270625423892205998681 4335952969067919154499011)
                  ·
                    refine ⟨6503929453601878731748517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335952969067919154499011 6503929453601878731748517)
                    ·
                      refine ⟨1219486772550352262202847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6503929453601878731748517 1219486772550352262202847)
                      ·
                        rfl

theorem cell23_2374942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2374942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374942 prefixEnd_2374942 := by exact prefixLift 2374942
  have htrace : WordTrace (prefixWord ++ tailWord_2374942) baseStart_2374942 baseEnd_2374942 := by
    simpa [prefixWord, tailWord_2374942, baseEnd_2374942] using wordTrace_append hprefix tailTrace_2374942
  have hstable : (prefixWord ++ tailWord_2374942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374942).length < 2 ^ (prefixWord ++ tailWord_2374942).sum := by decide
  have hdescent : baseEnd_2374942 < baseStart_2374942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374969 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 1, 4]
def baseStart_2374969 : Nat := 118140960795 + 2374969 * 2 ^ 59
def prefixEnd_2374969 : Nat := 4983230072969 + 3 ^ 40 * 2374969 * 2
def baseEnd_2374969 : Nat := 406500212176007885521741

theorem tailTrace_2374969 : CollatzResearch.WordTrace tailWord_2374969 prefixEnd_2374969 406500212176007885521741 := by
  unfold tailWord_2374969
  simp only [CollatzResearch.WordTrace]
  refine ⟨86622235732900400257855961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57748157155266933505237307 86622235732900400257855961)
  ·
    refine ⟨64966676799675300193391971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86622235732900400257855961 64966676799675300193391971)
    ·
      refine ⟨97450015199512950290087957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64966676799675300193391971 97450015199512950290087957)
      ·
        refine ⟨4567969462477169544847873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97450015199512950290087957 4567969462477169544847873)
        ·
          refine ⟨3425977096857877158635905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567969462477169544847873 3425977096857877158635905)
          ·
            refine ⟨2569482822643407868976929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425977096857877158635905 2569482822643407868976929)
            ·
              refine ⟨1927112116982555901732697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569482822643407868976929 1927112116982555901732697)
              ·
                refine ⟨1445334087736916926299523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927112116982555901732697 1445334087736916926299523)
                ·
                  refine ⟨2168001131605375389449285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445334087736916926299523 2168001131605375389449285)
                  ·
                    refine ⟨406500212176007885521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168001131605375389449285 406500212176007885521741)
                    ·
                      rfl

theorem cell23_2374969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_2374969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2374969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2374969 prefixEnd_2374969 := by exact prefixLift 2374969
  have htrace : WordTrace (prefixWord ++ tailWord_2374969) baseStart_2374969 baseEnd_2374969 := by
    simpa [prefixWord, tailWord_2374969, baseEnd_2374969] using wordTrace_append hprefix tailTrace_2374969
  have hstable : (prefixWord ++ tailWord_2374969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374969).length < 2 ^ (prefixWord ++ tailWord_2374969).sum := by decide
  have hdescent : baseEnd_2374969 < baseStart_2374969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375015 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2375015 : Nat := 118140960795 + 2375015 * 2 ^ 59
def prefixEnd_2375015 : Nat := 4983230072969 + 3 ^ 40 * 2375015 * 2
def baseEnd_2375015 : Nat := 1219524256638130476590011

theorem tailTrace_2375015 : CollatzResearch.WordTrace tailWord_2375015 prefixEnd_2375015 1219524256638130476590011 := by
  unfold tailWord_2375015
  simp only [CollatzResearch.WordTrace]
  refine ⟨86623913490733750114030499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57749275660489166742686999 86623913490733750114030499)
  ·
    refine ⟨129935870236100625171045749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86623913490733750114030499 129935870236100625171045749)
    ·
      refine ⟨12181487834634433609785539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129935870236100625171045749 12181487834634433609785539)
      ·
        refine ⟨18272231751951650414678309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12181487834634433609785539 18272231751951650414678309)
        ·
          refine ⟨3426043453490934452752183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18272231751951650414678309 3426043453490934452752183)
          ·
            refine ⟨5139065180236401679128275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426043453490934452752183 5139065180236401679128275)
            ·
              refine ⟨7708597770354602518692413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139065180236401679128275 7708597770354602518692413)
              ·
                refine ⟨2890724163882975944509655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7708597770354602518692413 2890724163882975944509655)
                ·
                  refine ⟨4336086245824463916764483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890724163882975944509655 4336086245824463916764483)
                  ·
                    refine ⟨6504129368736695875146725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336086245824463916764483 6504129368736695875146725)
                    ·
                      refine ⟨1219524256638130476590011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6504129368736695875146725 1219524256638130476590011)
                      ·
                        rfl

theorem cell23_2375015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2375015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375015 prefixEnd_2375015 := by exact prefixLift 2375015
  have htrace : WordTrace (prefixWord ++ tailWord_2375015) baseStart_2375015 baseEnd_2375015 := by
    simpa [prefixWord, tailWord_2375015, baseEnd_2375015] using wordTrace_append hprefix tailTrace_2375015
  have hstable : (prefixWord ++ tailWord_2375015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375015).length < 2 ^ (prefixWord ++ tailWord_2375015).sum := by decide
  have hdescent : baseEnd_2375015 < baseStart_2375015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375021 : List Nat := [1, 5, 1, 1, 1, 4, 10]
def baseStart_2375021 : Nat := 118140960795 + 2375021 * 2 ^ 59
def prefixEnd_2375021 : Nat := 4983230072969 + 3 ^ 40 * 2375021 * 2
def baseEnd_2375021 : Nat := 15055893055827869791543

theorem tailTrace_2375021 : CollatzResearch.WordTrace tailWord_2375021 prefixEnd_2375021 15055893055827869791543 := by
  unfold tailWord_2375021
  simp only [CollatzResearch.WordTrace]
  refine ⟨86624132328712013138748917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57749421552474675425832611 86624132328712013138748917)
  ·
    refine ⟨8121012405816751231757711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86624132328712013138748917 8121012405816751231757711)
    ·
      refine ⟨12181518608725126847636567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8121012405816751231757711 12181518608725126847636567)
      ·
        refine ⟨18272277913087690271454851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12181518608725126847636567 18272277913087690271454851)
        ·
          refine ⟨27408416869631535407182277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18272277913087690271454851 27408416869631535407182277)
          ·
            refine ⟨5139078163055912888846677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27408416869631535407182277 5139078163055912888846677)
            ·
              refine ⟨15055893055827869791543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5139078163055912888846677 15055893055827869791543)
              ·
                rfl

theorem cell23_2375021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 10].length) (baseStart_2375021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375021 prefixEnd_2375021 := by exact prefixLift 2375021
  have htrace : WordTrace (prefixWord ++ tailWord_2375021) baseStart_2375021 baseEnd_2375021 := by
    simpa [prefixWord, tailWord_2375021, baseEnd_2375021] using wordTrace_append hprefix tailTrace_2375021
  have hstable : (prefixWord ++ tailWord_2375021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375021).length < 2 ^ (prefixWord ++ tailWord_2375021).sum := by decide
  have hdescent : baseEnd_2375021 < baseStart_2375021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375042 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2375042 : Nat := 118140960795 + 2375042 * 2 ^ 59
def prefixEnd_2375042 : Nat := 4983230072969 + 3 ^ 40 * 2375042 * 2
def baseEnd_2375042 : Nat := 406512706871933956984129

theorem tailTrace_2375042 : CollatzResearch.WordTrace tailWord_2375042 prefixEnd_2375042 406512706871933956984129 := by
  unfold tailWord_2375042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656224565408983431315845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57749932174423955816842253 21656224565408983431315845)
  ·
    refine ⟨4060542106014184393371721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21656224565408983431315845 4060542106014184393371721)
    ·
      refine ⟨3045406579510638295028791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060542106014184393371721 3045406579510638295028791)
      ·
        refine ⟨4568109869265957442543187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045406579510638295028791 4568109869265957442543187)
        ·
          refine ⟨6852164803898936163814781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568109869265957442543187 6852164803898936163814781)
          ·
            refine ⟨2569561801462101061430543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6852164803898936163814781 2569561801462101061430543)
            ·
              refine ⟨3854342702193151592145815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569561801462101061430543 3854342702193151592145815)
              ·
                refine ⟨5781514053289727388218723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854342702193151592145815 5781514053289727388218723)
                ·
                  refine ⟨8672271079934591082328085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781514053289727388218723 8672271079934591082328085)
                  ·
                    refine ⟨406512706871933956984129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8672271079934591082328085 406512706871933956984129)
                    ·
                      rfl

theorem cell23_2375042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2375042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375042 prefixEnd_2375042 := by exact prefixLift 2375042
  have htrace : WordTrace (prefixWord ++ tailWord_2375042) baseStart_2375042 baseEnd_2375042 := by
    simpa [prefixWord, tailWord_2375042, baseEnd_2375042] using wordTrace_append hprefix tailTrace_2375042
  have hstable : (prefixWord ++ tailWord_2375042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375042).length < 2 ^ (prefixWord ++ tailWord_2375042).sum := by decide
  have hdescent : baseEnd_2375042 < baseStart_2375042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375061 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2375061 : Nat := 118140960795 + 2375061 * 2 ^ 59
def prefixEnd_2375061 : Nat := 4983230072969 + 3 ^ 40 * 2375061 * 2
def baseEnd_2375061 : Nat := 1219547876748237296614799

theorem tailTrace_2375061 : CollatzResearch.WordTrace tailWord_2375061 prefixEnd_2375061 1219547876748237296614799 := by
  unfold tailWord_2375061
  simp only [CollatzResearch.WordTrace]
  refine ⟨86625591248567099970205037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57750394165711399980136691 86625591248567099970205037)
  ·
    refine ⟨32484596718212662488826889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86625591248567099970205037 32484596718212662488826889)
    ·
      refine ⟨24363447538659496866620167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32484596718212662488826889 24363447538659496866620167)
      ·
        refine ⟨36545171307989245299930251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24363447538659496866620167 36545171307989245299930251)
        ·
          refine ⟨54817756961983867949895377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36545171307989245299930251 54817756961983867949895377)
          ·
            refine ⟨41113317721487900962421533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54817756961983867949895377 41113317721487900962421533)
            ·
              refine ⟨15417494145557962860908075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41113317721487900962421533 15417494145557962860908075)
              ·
                refine ⟨23126241218336944291362113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15417494145557962860908075 23126241218336944291362113)
                ·
                  refine ⟨17344680913752708218521585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23126241218336944291362113 17344680913752708218521585)
                  ·
                    refine ⟨13008510685314531163891189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17344680913752708218521585 13008510685314531163891189)
                    ·
                      refine ⟨1219547876748237296614799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13008510685314531163891189 1219547876748237296614799)
                      ·
                        rfl

theorem cell23_2375061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2375061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375061 prefixEnd_2375061 := by exact prefixLift 2375061
  have htrace : WordTrace (prefixWord ++ tailWord_2375061) baseStart_2375061 baseEnd_2375061 := by
    simpa [prefixWord, tailWord_2375061, baseEnd_2375061] using wordTrace_append hprefix tailTrace_2375061
  have hstable : (prefixWord ++ tailWord_2375061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375061).length < 2 ^ (prefixWord ++ tailWord_2375061).sum := by decide
  have hdescent : baseEnd_2375061 < baseStart_2375061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375075 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 1, 3, 2]
def baseStart_2375075 : Nat := 118140960795 + 2375075 * 2 ^ 59
def prefixEnd_2375075 : Nat := 4983230072969 + 3 ^ 40 * 2375075 * 2
def baseEnd_2375075 : Nat := 1219555065477400241839735

theorem tailTrace_2375075 : CollatzResearch.WordTrace tailWord_2375075 prefixEnd_2375075 1219555065477400241839735 := by
  unfold tailWord_2375075
  simp only [CollatzResearch.WordTrace]
  refine ⟨86626101870516380361214679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57750734580344253574143119 86626101870516380361214679)
  ·
    refine ⟨129939152805774570541822019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86626101870516380361214679 129939152805774570541822019)
    ·
      refine ⟨194908729208661855812733029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129939152805774570541822019 194908729208661855812733029)
      ·
        refine ⟨36545386726624097964887443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194908729208661855812733029 36545386726624097964887443)
        ·
          refine ⟨54818080089936146947331165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36545386726624097964887443 54818080089936146947331165)
          ·
            refine ⟨20556780033726055105249187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54818080089936146947331165 20556780033726055105249187)
            ·
              refine ⟨30835170050589082657873781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20556780033726055105249187 30835170050589082657873781)
              ·
                refine ⟨2890797192242726499175667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30835170050589082657873781 2890797192242726499175667)
                ·
                  refine ⟨4336195788364089748763501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890797192242726499175667 4336195788364089748763501)
                  ·
                    refine ⟨1626073420636533655786313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4336195788364089748763501 1626073420636533655786313)
                    ·
                      refine ⟨1219555065477400241839735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626073420636533655786313 1219555065477400241839735)
                      ·
                        rfl

theorem cell23_2375075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_2375075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375075 prefixEnd_2375075 := by exact prefixLift 2375075
  have htrace : WordTrace (prefixWord ++ tailWord_2375075) baseStart_2375075 baseEnd_2375075 := by
    simpa [prefixWord, tailWord_2375075, baseEnd_2375075] using wordTrace_append hprefix tailTrace_2375075
  have hstable : (prefixWord ++ tailWord_2375075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375075).length < 2 ^ (prefixWord ++ tailWord_2375075).sum := by decide
  have hdescent : baseEnd_2375075 < baseStart_2375075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375088 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2]
def baseStart_2375088 : Nat := 118140960795 + 2375088 * 2 ^ 59
def prefixEnd_2375088 : Nat := 4983230072969 + 3 ^ 40 * 2375088 * 2
def baseEnd_2375088 : Nat := 1219561740725908690977175

theorem tailTrace_2375088 : CollatzResearch.WordTrace tailWord_2375088 prefixEnd_2375088 1219561740725908690977175 := by
  unfold tailWord_2375088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43313288009734641790718959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57751050679646189054291945 43313288009734641790718959)
  ·
    refine ⟨64969932014601962686078439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43313288009734641790718959 64969932014601962686078439)
    ·
      refine ⟨97454898021902944029117659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64969932014601962686078439 97454898021902944029117659)
      ·
        refine ⟨146182347032854416043676489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97454898021902944029117659 146182347032854416043676489)
        ·
          refine ⟨109636760274640812032757367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146182347032854416043676489 109636760274640812032757367)
          ·
            refine ⟨164455140411961218049136051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109636760274640812032757367 164455140411961218049136051)
            ·
              refine ⟨246682710617941827073704077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164455140411961218049136051 246682710617941827073704077)
              ·
                refine ⟨92506016481728185152639029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246682710617941827073704077 92506016481728185152639029)
                ·
                  refine ⟨8672439045162017358059909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92506016481728185152639029 8672439045162017358059909)
                  ·
                    refine ⟨1626082320967878254636233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8672439045162017358059909 1626082320967878254636233)
                    ·
                      refine ⟨1219561740725908690977175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626082320967878254636233 1219561740725908690977175)
                      ·
                        rfl

theorem cell23_2375088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2].length) (baseStart_2375088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375088 prefixEnd_2375088 := by exact prefixLift 2375088
  have htrace : WordTrace (prefixWord ++ tailWord_2375088) baseStart_2375088 baseEnd_2375088 := by
    simpa [prefixWord, tailWord_2375088, baseEnd_2375088] using wordTrace_append hprefix tailTrace_2375088
  have hstable : (prefixWord ++ tailWord_2375088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375088).length < 2 ^ (prefixWord ++ tailWord_2375088).sum := by decide
  have hdescent : baseEnd_2375088 < baseStart_2375088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375111 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 9]
def baseStart_2375111 : Nat := 118140960795 + 2375111 * 2 ^ 59
def prefixEnd_2375111 : Nat := 4983230072969 + 3 ^ 40 * 2375111 * 2
def baseEnd_2375111 : Nat := 135508172308995788998841

theorem tailTrace_2375111 : CollatzResearch.WordTrace tailWord_2375111 prefixEnd_2375111 135508172308995788998841 := by
  unfold tailWord_2375111
  simp only [CollatzResearch.WordTrace]
  refine ⟨86627414898385958509525187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57751609932257305673016791 86627414898385958509525187)
  ·
    refine ⟨129941122347578937764287781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86627414898385958509525187 129941122347578937764287781)
    ·
      refine ⟨24363960440171050830803959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129941122347578937764287781 24363960440171050830803959)
      ·
        refine ⟨36545940660256576246205939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24363960440171050830803959 36545940660256576246205939)
        ·
          refine ⟨54818910990384864369308909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36545940660256576246205939 54818910990384864369308909)
          ·
            refine ⟨20557091621394324138490841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54818910990384864369308909 20557091621394324138490841)
            ·
              refine ⟨15417818716045743103868131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20557091621394324138490841 15417818716045743103868131)
              ·
                refine ⟨23126728074068614655802197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15417818716045743103868131 23126728074068614655802197)
                ·
                  refine ⟨135508172308995788998841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23126728074068614655802197 135508172308995788998841)
                  ·
                    rfl

theorem cell23_2375111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 9].length) (baseStart_2375111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375111 prefixEnd_2375111 := by exact prefixLift 2375111
  have htrace : WordTrace (prefixWord ++ tailWord_2375111) baseStart_2375111 baseEnd_2375111 := by
    simpa [prefixWord, tailWord_2375111, baseEnd_2375111] using wordTrace_append hprefix tailTrace_2375111
  have hstable : (prefixWord ++ tailWord_2375111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375111).length < 2 ^ (prefixWord ++ tailWord_2375111).sum := by decide
  have hdescent : baseEnd_2375111 < baseStart_2375111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375126 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2375126 : Nat := 118140960795 + 2375126 * 2 ^ 59
def prefixEnd_2375126 : Nat := 4983230072969 + 3 ^ 40 * 2375126 * 2
def baseEnd_2375126 : Nat := 1219581252990779542302001

theorem tailTrace_2375126 : CollatzResearch.WordTrace tailWord_2375126 prefixEnd_2375126 1219581252990779542302001 := by
  unfold tailWord_2375126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414247624583226004457577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57751974662221077380880821 5414247624583226004457577)
  ·
    refine ⟨4060685718437419503343183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5414247624583226004457577 4060685718437419503343183)
    ·
      refine ⟨6091028577656129255014775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060685718437419503343183 6091028577656129255014775)
      ·
        refine ⟨9136542866484193882522163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091028577656129255014775 9136542866484193882522163)
        ·
          refine ⟨13704814299726290823783245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136542866484193882522163 13704814299726290823783245)
          ·
            refine ⟨5139305362397359058918717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13704814299726290823783245 5139305362397359058918717)
            ·
              refine ⟨1927239510899009647094519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5139305362397359058918717 1927239510899009647094519)
              ·
                refine ⟨2890859266348514470641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927239510899009647094519 2890859266348514470641779)
                ·
                  refine ⟨4336288899522771705962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890859266348514470641779 4336288899522771705962669)
                  ·
                    refine ⟨1626108337321039389736001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4336288899522771705962669 1626108337321039389736001)
                    ·
                      refine ⟨1219581252990779542302001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626108337321039389736001 1219581252990779542302001)
                      ·
                        rfl

theorem cell23_2375126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2375126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375126 prefixEnd_2375126 := by exact prefixLift 2375126
  have htrace : WordTrace (prefixWord ++ tailWord_2375126) baseStart_2375126 baseEnd_2375126 := by
    simpa [prefixWord, tailWord_2375126, baseEnd_2375126] using wordTrace_append hprefix tailTrace_2375126
  have hstable : (prefixWord ++ tailWord_2375126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375126).length < 2 ^ (prefixWord ++ tailWord_2375126).sum := by decide
  have hdescent : baseEnd_2375126 < baseStart_2375126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375139 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 2, 2, 2]
def baseStart_2375139 : Nat := 118140960795 + 2375139 * 2 ^ 59
def prefixEnd_2375139 : Nat := 4983230072969 + 3 ^ 40 * 2375139 * 2
def baseEnd_2375139 : Nat := 1219587928239287991439441

theorem tailTrace_2375139 : CollatzResearch.WordTrace tailWord_2375139 prefixEnd_2375139 1219587928239287991439441 := by
  unfold tailWord_2375139
  simp only [CollatzResearch.WordTrace]
  refine ⟨86628436142284519291544471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57752290761523012861029647 86628436142284519291544471)
  ·
    refine ⟨129942654213426778937316707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86628436142284519291544471 129942654213426778937316707)
    ·
      refine ⟨194913981320140168405975061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129942654213426778937316707 194913981320140168405975061)
      ·
        refine ⟨9136592874381570394030081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194913981320140168405975061 9136592874381570394030081)
        ·
          refine ⟨6852444655786177795522561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9136592874381570394030081 6852444655786177795522561)
          ·
            refine ⟨5139333491839633346641921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6852444655786177795522561 5139333491839633346641921)
            ·
              refine ⟨3854500118879725009981441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139333491839633346641921 3854500118879725009981441)
              ·
                refine ⟨2890875089159793757486081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854500118879725009981441 2890875089159793757486081)
                ·
                  refine ⟨2168156316869845318114561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2890875089159793757486081 2168156316869845318114561)
                  ·
                    refine ⟨1626117237652383988585921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168156316869845318114561 1626117237652383988585921)
                    ·
                      refine ⟨1219587928239287991439441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626117237652383988585921 1219587928239287991439441)
                      ·
                        rfl

theorem cell23_2375139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_2375139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375139 prefixEnd_2375139 := by exact prefixLift 2375139
  have htrace : WordTrace (prefixWord ++ tailWord_2375139) baseStart_2375139 baseEnd_2375139 := by
    simpa [prefixWord, tailWord_2375139, baseEnd_2375139] using wordTrace_append hprefix tailTrace_2375139
  have hstable : (prefixWord ++ tailWord_2375139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375139).length < 2 ^ (prefixWord ++ tailWord_2375139).sum := by decide
  have hdescent : baseEnd_2375139 < baseStart_2375139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375171 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 10]
def baseStart_2375171 : Nat := 118140960795 + 2375171 * 2 ^ 59
def prefixEnd_2375171 : Nat := 4983230072969 + 3 ^ 40 * 2375171 * 2
def baseEnd_2375171 : Nat := 406534786540077288746431

theorem tailTrace_2375171 : CollatzResearch.WordTrace tailWord_2375171 prefixEnd_2375171 406534786540077288746431 := by
  unfold tailWord_2375171
  simp only [CollatzResearch.WordTrace]
  refine ⟨86629603278168588756709367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57753068852112392504472911 86629603278168588756709367)
  ·
    refine ⟨129944404917252883135064051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86629603278168588756709367 129944404917252883135064051)
    ·
      refine ⟨194916607375879324702596077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129944404917252883135064051 194916607375879324702596077)
      ·
        refine ⟨73093727765954746763473529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194916607375879324702596077 73093727765954746763473529)
        ·
          refine ⟨54820295824466060072605147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73093727765954746763473529 54820295824466060072605147)
          ·
            refine ⟨82230443736699090108907721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54820295824466060072605147 82230443736699090108907721)
            ·
              refine ⟨61672832802524317581680791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82230443736699090108907721 61672832802524317581680791)
              ·
                refine ⟨92509249203786476372521187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61672832802524317581680791 92509249203786476372521187)
                ·
                  refine ⟨138763873805679714558781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92509249203786476372521187 138763873805679714558781781)
                  ·
                    refine ⟨406534786540077288746431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 138763873805679714558781781 406534786540077288746431)
                    ·
                      rfl

theorem cell23_2375171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_2375171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375171 prefixEnd_2375171 := by exact prefixLift 2375171
  have htrace : WordTrace (prefixWord ++ tailWord_2375171) baseStart_2375171 baseEnd_2375171 := by
    simpa [prefixWord, tailWord_2375171, baseEnd_2375171] using wordTrace_append hprefix tailTrace_2375171
  have hstable : (prefixWord ++ tailWord_2375171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375171).length < 2 ^ (prefixWord ++ tailWord_2375171).sum := by decide
  have hdescent : baseEnd_2375171 < baseStart_2375171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375175 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 2, 5]
def baseStart_2375175 : Nat := 118140960795 + 2375175 * 2 ^ 59
def prefixEnd_2375175 : Nat := 4983230072969 + 3 ^ 40 * 2375175 * 2
def baseEnd_2375175 : Nat := 406535471180949950196425

theorem tailTrace_2375175 : CollatzResearch.WordTrace tailWord_2375175 prefixEnd_2375175 406535471180949950196425 := by
  unfold tailWord_2375175
  simp only [CollatzResearch.WordTrace]
  refine ⟨86629749170154097439854979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57753166113436064959903319 86629749170154097439854979)
  ·
    refine ⟨129944623755231146159782469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86629749170154097439854979 129944623755231146159782469)
    ·
      refine ⟨24364616954105839904959213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129944623755231146159782469 24364616954105839904959213)
      ·
        refine ⟨9136731357789689964359705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24364616954105839904959213 9136731357789689964359705)
        ·
          refine ⟨6852548518342267473269779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9136731357789689964359705 6852548518342267473269779)
          ·
            refine ⟨10278822777513401209904669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852548518342267473269779 10278822777513401209904669)
            ·
              refine ⟨3854558541567525453714251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10278822777513401209904669 3854558541567525453714251)
              ·
                refine ⟨5781837812351288180571377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854558541567525453714251 5781837812351288180571377)
                ·
                  refine ⟨4336378359263466135428533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781837812351288180571377 4336378359263466135428533)
                  ·
                    refine ⟨406535471180949950196425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4336378359263466135428533 406535471180949950196425)
                    ·
                      rfl

theorem cell23_2375175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_2375175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375175 prefixEnd_2375175 := by exact prefixLift 2375175
  have htrace : WordTrace (prefixWord ++ tailWord_2375175) baseStart_2375175 baseEnd_2375175 := by
    simpa [prefixWord, tailWord_2375175, baseEnd_2375175] using wordTrace_append hprefix tailTrace_2375175
  have hstable : (prefixWord ++ tailWord_2375175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375175).length < 2 ^ (prefixWord ++ tailWord_2375175).sum := by decide
  have hdescent : baseEnd_2375175 < baseStart_2375175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375282 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_2375282 : Nat := 118140960795 + 2375282 * 2 ^ 59
def prefixEnd_2375282 : Nat := 4983230072969 + 3 ^ 40 * 2375282 * 2
def baseEnd_2375282 : Nat := 406553785324293643983761

theorem tailTrace_2375282 : CollatzResearch.WordTrace tailWord_2375282 prefixEnd_2375282 406553785324293643983761 := by
  unfold tailWord_2375282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658412945191613678500025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57755767853844303142666733 21658412945191613678500025)
  ·
    refine ⟨16243809708893710258875019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21658412945191613678500025 16243809708893710258875019)
    ·
      refine ⟨24365714563340565388312529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16243809708893710258875019 24365714563340565388312529)
      ·
        refine ⟨18274285922505424041234397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24365714563340565388312529 18274285922505424041234397)
        ·
          refine ⟨6852857220939534015462899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18274285922505424041234397 6852857220939534015462899)
          ·
            refine ⟨10279285831409301023194349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852857220939534015462899 10279285831409301023194349)
            ·
              refine ⟨3854732186778487883697881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10279285831409301023194349 3854732186778487883697881)
              ·
                refine ⟨2891049140083865912773411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854732186778487883697881 2891049140083865912773411)
                ·
                  refine ⟨4336573710125798869160117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891049140083865912773411 4336573710125798869160117)
                  ·
                    refine ⟨406553785324293643983761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4336573710125798869160117 406553785324293643983761)
                    ·
                      rfl

theorem cell23_2375282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_2375282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375282 prefixEnd_2375282 := by exact prefixLift 2375282
  have htrace : WordTrace (prefixWord ++ tailWord_2375282) baseStart_2375282 baseEnd_2375282 := by
    simpa [prefixWord, tailWord_2375282, baseEnd_2375282] using wordTrace_append hprefix tailTrace_2375282
  have hstable : (prefixWord ++ tailWord_2375282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375282).length < 2 ^ (prefixWord ++ tailWord_2375282).sum := by decide
  have hdescent : baseEnd_2375282 < baseStart_2375282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375305 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_2375305 : Nat := 118140960795 + 2375305 * 2 ^ 59
def prefixEnd_2375305 : Nat := 4983230072969 + 3 ^ 40 * 2375305 * 2
def baseEnd_2375305 : Nat := 1219673166027934341963677

theorem tailTrace_2375305 : CollatzResearch.WordTrace tailWord_2375305 prefixEnd_2375305 1219673166027934341963677 := by
  unfold tailWord_2375305
  simp only [CollatzResearch.WordTrace]
  refine ⟨86634490659683129642087369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57756327106455419761391579 86634490659683129642087369)
  ·
    refine ⟨64975867994762347231565527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86634490659683129642087369 64975867994762347231565527)
    ·
      refine ⟨97463801992143520847348291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64975867994762347231565527 97463801992143520847348291)
      ·
        refine ⟨146195702988215281271022437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97463801992143520847348291 146195702988215281271022437)
        ·
          refine ⟨27411694310290365238316707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146195702988215281271022437 27411694310290365238316707)
          ·
            refine ⟨41117541465435547857475061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27411694310290365238316707 41117541465435547857475061)
            ·
              refine ⟨3854769512384582611638287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41117541465435547857475061 3854769512384582611638287)
              ·
                refine ⟨5782154268576873917457431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854769512384582611638287 5782154268576873917457431)
                ·
                  refine ⟨8673231402865310876186147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782154268576873917457431 8673231402865310876186147)
                  ·
                    refine ⟨13009847104297966314279221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8673231402865310876186147 13009847104297966314279221)
                    ·
                      refine ⟨1219673166027934341963677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13009847104297966314279221 1219673166027934341963677)
                      ·
                        rfl

theorem cell23_2375305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_2375305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375305 prefixEnd_2375305 := by exact prefixLift 2375305
  have htrace : WordTrace (prefixWord ++ tailWord_2375305) baseStart_2375305 baseEnd_2375305 := by
    simpa [prefixWord, tailWord_2375305, baseEnd_2375305] using wordTrace_append hprefix tailTrace_2375305
  have hstable : (prefixWord ++ tailWord_2375305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375305).length < 2 ^ (prefixWord ++ tailWord_2375305).sum := by decide
  have hdescent : baseEnd_2375305 < baseStart_2375305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375332 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_2375332 : Nat := 118140960795 + 2375332 * 2 ^ 59
def prefixEnd_2375332 : Nat := 4983230072969 + 3 ^ 40 * 2375332 * 2
def baseEnd_2375332 : Nat := 1219687030005605736326053

theorem tailTrace_2375332 : CollatzResearch.WordTrace tailWord_2375332 prefixEnd_2375332 1219687030005605736326053 := by
  unfold tailWord_2375332
  simp only [CollatzResearch.WordTrace]
  refine ⟨43317737715292656626660125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57756983620390208835546833 43317737715292656626660125)
  ·
    refine ⟨16244151643234746234997547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43317737715292656626660125 16244151643234746234997547)
    ·
      refine ⟨24366227464852119352496321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244151643234746234997547 24366227464852119352496321)
      ·
        refine ⟨18274670598639089514372241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24366227464852119352496321 18274670598639089514372241)
        ·
          refine ⟨13706002948979317135779181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18274670598639089514372241 13706002948979317135779181)
          ·
            refine ⟨5139751105867243925917193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13706002948979317135779181 5139751105867243925917193)
            ·
              refine ⟨3854813329400432944437895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139751105867243925917193 3854813329400432944437895)
              ·
                refine ⟨5782219994100649416656843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854813329400432944437895 5782219994100649416656843)
                ·
                  refine ⟨8673329991150974124985265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782219994100649416656843 8673329991150974124985265)
                  ·
                    refine ⟨6504997493363230593738949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8673329991150974124985265 6504997493363230593738949)
                    ·
                      refine ⟨1219687030005605736326053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6504997493363230593738949 1219687030005605736326053)
                      ·
                        rfl

theorem cell23_2375332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_2375332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375332 prefixEnd_2375332 := by exact prefixLift 2375332
  have htrace : WordTrace (prefixWord ++ tailWord_2375332) baseStart_2375332 baseEnd_2375332 := by
    simpa [prefixWord, tailWord_2375332, baseEnd_2375332] using wordTrace_append hprefix tailTrace_2375332
  have hstable : (prefixWord ++ tailWord_2375332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375332).length < 2 ^ (prefixWord ++ tailWord_2375332).sum := by decide
  have hdescent : baseEnd_2375332 < baseStart_2375332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375356 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_2375356 : Nat := 118140960795 + 2375356 * 2 ^ 59
def prefixEnd_2375356 : Nat := 4983230072969 + 3 ^ 40 * 2375356 * 2
def baseEnd_2375356 : Nat := 1219699353541313642425943

theorem tailTrace_2375356 : CollatzResearch.WordTrace tailWord_2375356 prefixEnd_2375356 1219699353541313642425943 := by
  unfold tailWord_2375356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43318175391249182676096961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57757567188332243568129281 43318175391249182676096961)
  ·
    refine ⟨32488631543436887007072721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43318175391249182676096961 32488631543436887007072721)
    ·
      refine ⟨24366473657577665255304541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32488631543436887007072721 24366473657577665255304541)
      ·
        refine ⟨9137427621591624470739203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24366473657577665255304541 9137427621591624470739203)
        ·
          refine ⟨13706141432387436706108805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137427621591624470739203 13706141432387436706108805)
          ·
            refine ⟨2569901518572644382395401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13706141432387436706108805 2569901518572644382395401)
            ·
              refine ⟨1927426138929483286796551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569901518572644382395401 1927426138929483286796551)
              ·
                refine ⟨2891139208394224930194827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927426138929483286796551 2891139208394224930194827)
                ·
                  refine ⟨4336708812591337395292241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891139208394224930194827 4336708812591337395292241)
                  ·
                    refine ⟨3252531609443503046469181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4336708812591337395292241 3252531609443503046469181)
                    ·
                      refine ⟨1219699353541313642425943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252531609443503046469181 1219699353541313642425943)
                      ·
                        rfl

theorem cell23_2375356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_2375356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375356 prefixEnd_2375356 := by exact prefixLift 2375356
  have htrace : WordTrace (prefixWord ++ tailWord_2375356) baseStart_2375356 baseEnd_2375356 := by
    simpa [prefixWord, tailWord_2375356, baseEnd_2375356] using wordTrace_append hprefix tailTrace_2375356
  have hstable : (prefixWord ++ tailWord_2375356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375356).length < 2 ^ (prefixWord ++ tailWord_2375356).sum := by decide
  have hdescent : baseEnd_2375356 < baseStart_2375356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375385 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_2375385 : Nat := 118140960795 + 2375385 * 2 ^ 59
def prefixEnd_2375385 : Nat := 4983230072969 + 3 ^ 40 * 2375385 * 2
def baseEnd_2375385 : Nat := 406571414826764676321103

theorem tailTrace_2375385 : CollatzResearch.WordTrace tailWord_2375385 prefixEnd_2375385 406571414826764676321103 := by
  unfold tailWord_2375385
  simp only [CollatzResearch.WordTrace]
  refine ⟨86637408499393303304999609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57758272332928868869999739 86637408499393303304999609)
  ·
    refine ⟨64978056374544977478749707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86637408499393303304999609 64978056374544977478749707)
    ·
      refine ⟨97467084561817466218124561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64978056374544977478749707 97467084561817466218124561)
      ·
        refine ⟨73100313421363099663593421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97467084561817466218124561 73100313421363099663593421)
        ·
          refine ⟨27412617533011162373847533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73100313421363099663593421 27412617533011162373847533)
          ·
            refine ⟨10279731574879185890192825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27412617533011162373847533 10279731574879185890192825)
            ·
              refine ⟨7709798681159389417644619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10279731574879185890192825 7709798681159389417644619)
              ·
                refine ⟨11564698021739084126466929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709798681159389417644619 11564698021739084126466929)
                ·
                  refine ⟨8673523516304313094850197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11564698021739084126466929 8673523516304313094850197)
                  ·
                    refine ⟨406571414826764676321103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8673523516304313094850197 406571414826764676321103)
                    ·
                      rfl

theorem cell23_2375385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_2375385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375385 prefixEnd_2375385 := by exact prefixLift 2375385
  have htrace : WordTrace (prefixWord ++ tailWord_2375385) baseStart_2375385 baseEnd_2375385 := by
    simpa [prefixWord, tailWord_2375385, baseEnd_2375385] using wordTrace_append hprefix tailTrace_2375385
  have hstable : (prefixWord ++ tailWord_2375385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375385).length < 2 ^ (prefixWord ++ tailWord_2375385).sum := by decide
  have hdescent : baseEnd_2375385 < baseStart_2375385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375386 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_2375386 : Nat := 118140960795 + 2375386 * 2 ^ 59
def prefixEnd_2375386 : Nat := 4983230072969 + 3 ^ 40 * 2375386 * 2
def baseEnd_2375386 : Nat := 1219714757960948525050805

theorem tailTrace_2375386 : CollatzResearch.WordTrace tailWord_2375386 prefixEnd_2375386 1219714757960948525050805 := by
  unfold tailWord_2375386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659361243097420118946503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57758296648259786983857341 21659361243097420118946503)
  ·
    refine ⟨32489041864646130178419755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21659361243097420118946503 32489041864646130178419755)
    ·
      refine ⟨48733562796969195267629633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32489041864646130178419755 48733562796969195267629633)
      ·
        refine ⟨36550172097726896450722225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48733562796969195267629633 36550172097726896450722225)
        ·
          refine ⟨27412629073295172338041669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36550172097726896450722225 27412629073295172338041669)
          ·
            refine ⟨5139867951242844813382813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27412629073295172338041669 5139867951242844813382813)
            ·
              refine ⟨1927450481716066805018555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5139867951242844813382813 1927450481716066805018555)
              ·
                refine ⟨2891175722574100207527833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927450481716066805018555 2891175722574100207527833)
                ·
                  refine ⟨2168381791930575155645875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891175722574100207527833 2168381791930575155645875)
                  ·
                    refine ⟨3252572687895862733468813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2168381791930575155645875 3252572687895862733468813)
                    ·
                      refine ⟨1219714757960948525050805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252572687895862733468813 1219714757960948525050805)
                      ·
                        rfl

theorem cell23_2375386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_2375386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375386 prefixEnd_2375386 := by exact prefixLift 2375386
  have htrace : WordTrace (prefixWord ++ tailWord_2375386) baseStart_2375386 baseEnd_2375386 := by
    simpa [prefixWord, tailWord_2375386, baseEnd_2375386] using wordTrace_append hprefix tailTrace_2375386
  have hstable : (prefixWord ++ tailWord_2375386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375386).length < 2 ^ (prefixWord ++ tailWord_2375386).sum := by decide
  have hdescent : baseEnd_2375386 < baseStart_2375386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375409 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_2375409 : Nat := 118140960795 + 2375409 * 2 ^ 59
def prefixEnd_2375409 : Nat := 4983230072969 + 3 ^ 40 * 2375409 * 2
def baseEnd_2375409 : Nat := 1219726568016001935063199

theorem tailTrace_2375409 : CollatzResearch.WordTrace tailWord_2375409 prefixEnd_2375409 1219726568016001935063199 := by
  unfold tailWord_2375409
  simp only [CollatzResearch.WordTrace]
  refine ⟨86638283851306355403873281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57758855900870903602582187 86638283851306355403873281)
  ·
    refine ⟨64978712888479766552904961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86638283851306355403873281 64978712888479766552904961)
    ·
      refine ⟨48734034666359824914678721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64978712888479766552904961 48734034666359824914678721)
      ·
        refine ⟨36550525999769868686009041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48734034666359824914678721 36550525999769868686009041)
        ·
          refine ⟨27412894499827401514506781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36550525999769868686009041 27412894499827401514506781)
          ·
            refine ⟨10279835437435275567940043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27412894499827401514506781 10279835437435275567940043)
            ·
              refine ⟨15419753156152913351910065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10279835437435275567940043 15419753156152913351910065)
              ·
                refine ⟨11564814867114685013932549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15419753156152913351910065 11564814867114685013932549)
                ·
                  refine ⟨2168402787584003440112353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11564814867114685013932549 2168402787584003440112353)
                  ·
                    refine ⟨1626302090688002580084265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168402787584003440112353 1626302090688002580084265)
                    ·
                      refine ⟨1219726568016001935063199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626302090688002580084265 1219726568016001935063199)
                      ·
                        rfl

theorem cell23_2375409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_2375409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375409 prefixEnd_2375409 := by exact prefixLift 2375409
  have htrace : WordTrace (prefixWord ++ tailWord_2375409) baseStart_2375409 baseEnd_2375409 := by
    simpa [prefixWord, tailWord_2375409, baseEnd_2375409] using wordTrace_append hprefix tailTrace_2375409
  have hstable : (prefixWord ++ tailWord_2375409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375409).length < 2 ^ (prefixWord ++ tailWord_2375409).sum := by decide
  have hdescent : baseEnd_2375409 < baseStart_2375409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375426 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2375426 : Nat := 118140960795 + 2375426 * 2 ^ 59
def prefixEnd_2375426 : Nat := 4983230072969 + 3 ^ 40 * 2375426 * 2
def baseEnd_2375426 : Nat := 1219735297187128368550621

theorem tailTrace_2375426 : CollatzResearch.WordTrace tailWord_2375426 prefixEnd_2375426 1219735297187128368550621 := by
  unfold tailWord_2375426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659725973061191826810533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57759269261496511538161421 21659725973061191826810533)
  ·
    refine ⟨4061198619948973467526975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21659725973061191826810533 4061198619948973467526975)
    ·
      refine ⟨6091797929923460201290463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061198619948973467526975 6091797929923460201290463)
      ·
        refine ⟨9137696894885190301935695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091797929923460201290463 9137696894885190301935695)
        ·
          refine ⟨13706545342327785452903543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137696894885190301935695 13706545342327785452903543)
          ·
            refine ⟨20559818013491678179355315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706545342327785452903543 20559818013491678179355315)
            ·
              refine ⟨30839727020237517269032973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20559818013491678179355315 30839727020237517269032973)
              ·
                refine ⟨11564897632589068975887365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30839727020237517269032973 11564897632589068975887365)
                ·
                  refine ⟨2168418306110450432978881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11564897632589068975887365 2168418306110450432978881)
                  ·
                    refine ⟨1626313729582837824734161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168418306110450432978881 1626313729582837824734161)
                    ·
                      refine ⟨1219735297187128368550621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626313729582837824734161 1219735297187128368550621)
                      ·
                        rfl

theorem cell23_2375426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2375426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375426 prefixEnd_2375426 := by exact prefixLift 2375426
  have htrace : WordTrace (prefixWord ++ tailWord_2375426) baseStart_2375426 baseEnd_2375426 := by
    simpa [prefixWord, tailWord_2375426, baseEnd_2375426] using wordTrace_append hprefix tailTrace_2375426
  have hstable : (prefixWord ++ tailWord_2375426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375426).length < 2 ^ (prefixWord ++ tailWord_2375426).sum := by decide
  have hdescent : baseEnd_2375426 < baseStart_2375426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375437 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2375437 : Nat := 118140960795 + 2375437 * 2 ^ 59
def prefixEnd_2375437 : Nat := 4983230072969 + 3 ^ 40 * 2375437 * 2
def baseEnd_2375437 : Nat := 1219740945474327825513071

theorem tailTrace_2375437 : CollatzResearch.WordTrace tailWord_2375437 prefixEnd_2375437 1219740945474327825513071 := by
  unfold tailWord_2375437
  simp only [CollatzResearch.WordTrace]
  refine ⟨86639305095204916185892565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57759536730136610790595043 86639305095204916185892565)
  ·
    refine ⟨2030608713168865223106857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 86639305095204916185892565 2030608713168865223106857)
    ·
      refine ⟨1522956534876648917330143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2030608713168865223106857 1522956534876648917330143)
      ·
        refine ⟨2284434802314973375995215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522956534876648917330143 2284434802314973375995215)
        ·
          refine ⟨3426652203472460063992823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284434802314973375995215 3426652203472460063992823)
          ·
            refine ⟨5139978305208690095989235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426652203472460063992823 5139978305208690095989235)
            ·
              refine ⟨7709967457813035143983853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139978305208690095989235 7709967457813035143983853)
              ·
                refine ⟨2891237796679888178993945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7709967457813035143983853 2891237796679888178993945)
                ·
                  refine ⟨2168428347509916134245459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891237796679888178993945 2168428347509916134245459)
                  ·
                    refine ⟨3252642521264874201368189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2168428347509916134245459 3252642521264874201368189)
                    ·
                      refine ⟨1219740945474327825513071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252642521264874201368189 1219740945474327825513071)
                      ·
                        rfl

theorem cell23_2375437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2375437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375437 prefixEnd_2375437 := by exact prefixLift 2375437
  have htrace : WordTrace (prefixWord ++ tailWord_2375437) baseStart_2375437 baseEnd_2375437 := by
    simpa [prefixWord, tailWord_2375437, baseEnd_2375437] using wordTrace_append hprefix tailTrace_2375437
  have hstable : (prefixWord ++ tailWord_2375437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375437).length < 2 ^ (prefixWord ++ tailWord_2375437).sum := by decide
  have hdescent : baseEnd_2375437 < baseStart_2375437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375455 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2375455 : Nat := 118140960795 + 2375455 * 2 ^ 59
def prefixEnd_2375455 : Nat := 4983230072969 + 3 ^ 40 * 2375455 * 2
def baseEnd_2375455 : Nat := 1219750188126108755087987

theorem tailTrace_2375455 : CollatzResearch.WordTrace tailWord_2375455 prefixEnd_2375455 1219750188126108755087987 := by
  unfold tailWord_2375455
  simp only [CollatzResearch.WordTrace]
  refine ⟨86639961609139705260047819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57759974406093136840031879 86639961609139705260047819)
  ·
    refine ⟨129959942413709557890071729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86639961609139705260047819 129959942413709557890071729)
    ·
      refine ⟨97469956810282168417553797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129959942413709557890071729 97469956810282168417553797)
      ·
        refine ⟨18275616901927906578291337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97469956810282168417553797 18275616901927906578291337)
        ·
          refine ⟨13706712676445929933718503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18275616901927906578291337 13706712676445929933718503)
          ·
            refine ⟨20560069014668894900577755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706712676445929933718503 20560069014668894900577755)
            ·
              refine ⟨30840103522003342350866633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20560069014668894900577755 30840103522003342350866633)
              ·
                refine ⟨23130077641502506763149975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30840103522003342350866633 23130077641502506763149975)
                ·
                  refine ⟨34695116462253760144724963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23130077641502506763149975 34695116462253760144724963)
                  ·
                    refine ⟨52042674693380640217087445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34695116462253760144724963 52042674693380640217087445)
                    ·
                      refine ⟨1219750188126108755087987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52042674693380640217087445 1219750188126108755087987)
                      ·
                        rfl

theorem cell23_2375455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2375455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375455 prefixEnd_2375455 := by exact prefixLift 2375455
  have htrace : WordTrace (prefixWord ++ tailWord_2375455) baseStart_2375455 baseEnd_2375455 := by
    simpa [prefixWord, tailWord_2375455, baseEnd_2375455] using wordTrace_append hprefix tailTrace_2375455
  have hstable : (prefixWord ++ tailWord_2375455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375455).length < 2 ^ (prefixWord ++ tailWord_2375455).sum := by decide
  have hdescent : baseEnd_2375455 < baseStart_2375455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375509 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2375509 : Nat := 118140960795 + 2375509 * 2 ^ 59
def prefixEnd_2375509 : Nat := 4983230072969 + 3 ^ 40 * 2375509 * 2
def baseEnd_2375509 : Nat := 406592638693817181270913

theorem tailTrace_2375509 : CollatzResearch.WordTrace tailWord_2375509 prefixEnd_2375509 406592638693817181270913 := by
  unfold tailWord_2375509
  simp only [CollatzResearch.WordTrace]
  refine ⟨86641931150944072482513581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57761287433962714988342387 86641931150944072482513581)
  ·
    refine ⟨32490724181604027180942593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86641931150944072482513581 32490724181604027180942593)
    ·
      refine ⟨24368043136203020385706945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32490724181604027180942593 24368043136203020385706945)
      ·
        refine ⟨18276032352152265289280209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24368043136203020385706945 18276032352152265289280209)
        ·
          refine ⟨13707024264114198966960157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18276032352152265289280209 13707024264114198966960157)
          ·
            refine ⟨5140134099042824612610059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13707024264114198966960157 5140134099042824612610059)
            ·
              refine ⟨7710201148564236918915089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140134099042824612610059 7710201148564236918915089)
              ·
                refine ⟨5782650861423177689186317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7710201148564236918915089 5782650861423177689186317)
                ·
                  refine ⟨2168494073033691633444869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5782650861423177689186317 2168494073033691633444869)
                  ·
                    refine ⟨406592638693817181270913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168494073033691633444869 406592638693817181270913)
                    ·
                      rfl

theorem cell23_2375509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2375509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375509 prefixEnd_2375509 := by exact prefixLift 2375509
  have htrace : WordTrace (prefixWord ++ tailWord_2375509) baseStart_2375509 baseEnd_2375509 := by
    simpa [prefixWord, tailWord_2375509, baseEnd_2375509] using wordTrace_append hprefix tailTrace_2375509
  have hstable : (prefixWord ++ tailWord_2375509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375509).length < 2 ^ (prefixWord ++ tailWord_2375509).sum := by decide
  have hdescent : baseEnd_2375509 < baseStart_2375509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375519 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2375519 : Nat := 118140960795 + 2375519 * 2 ^ 59
def prefixEnd_2375519 : Nat := 4983230072969 + 3 ^ 40 * 2375519 * 2
def baseEnd_2375519 : Nat := 1219783050887996504687693

theorem tailTrace_2375519 : CollatzResearch.WordTrace tailWord_2375519 prefixEnd_2375519 1219783050887996504687693 := by
  unfold tailWord_2375519
  simp only [CollatzResearch.WordTrace]
  refine ⟨86642295880907844190377611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57761530587271896126918407 86642295880907844190377611)
  ·
    refine ⟨129963443821361766285566417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86642295880907844190377611 129963443821361766285566417)
    ·
      refine ⟨97472582866021324714174813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129963443821361766285566417 97472582866021324714174813)
      ·
        refine ⟨36552218574757996767815555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97472582866021324714174813 36552218574757996767815555)
        ·
          refine ⟨54828327862136995151723333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36552218574757996767815555 54828327862136995151723333)
          ·
            refine ⟨10280311474150686590948125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54828327862136995151723333 10280311474150686590948125)
            ·
              refine ⟨3855116802806507471605547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10280311474150686590948125 3855116802806507471605547)
              ·
                refine ⟨5782675204209761207408321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855116802806507471605547 5782675204209761207408321)
                ·
                  refine ⟨4337006403157320905556241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5782675204209761207408321 4337006403157320905556241)
                  ·
                    refine ⟨3252754802367990679167181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337006403157320905556241 3252754802367990679167181)
                    ·
                      refine ⟨1219783050887996504687693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252754802367990679167181 1219783050887996504687693)
                      ·
                        rfl

theorem cell23_2375519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2375519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375519 prefixEnd_2375519 := by exact prefixLift 2375519
  have htrace : WordTrace (prefixWord ++ tailWord_2375519) baseStart_2375519 baseEnd_2375519 := by
    simpa [prefixWord, tailWord_2375519, baseEnd_2375519] using wordTrace_append hprefix tailTrace_2375519
  have hstable : (prefixWord ++ tailWord_2375519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375519).length < 2 ^ (prefixWord ++ tailWord_2375519).sum := by decide
  have hdescent : baseEnd_2375519 < baseStart_2375519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375599 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 2, 4]
def baseStart_2375599 : Nat := 118140960795 + 2375599 * 2 ^ 59
def prefixEnd_2375599 : Nat := 4983230072969 + 3 ^ 40 * 2375599 * 2
def baseEnd_2375599 : Nat := 406608043113452063895775

theorem tailTrace_2375599 : CollatzResearch.WordTrace tailWord_2375599 prefixEnd_2375599 406608043113452063895775 := by
  unfold tailWord_2375599
  simp only [CollatzResearch.WordTrace]
  refine ⟨86645213720618017853289851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57763475813745345235526567 86645213720618017853289851)
  ·
    refine ⟨129967820580927026779934777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86645213720618017853289851 129967820580927026779934777)
    ·
      refine ⟨97475865435695270084951083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129967820580927026779934777 97475865435695270084951083)
      ·
        refine ⟨146213798153542905127426625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97475865435695270084951083 146213798153542905127426625)
        ·
          refine ⟨109660348615157178845569969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146213798153542905127426625 109660348615157178845569969)
          ·
            refine ⟨82245261461367884134177477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109660348615157178845569969 82245261461367884134177477)
            ·
              refine ⟨15420986524006478275158277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82245261461367884134177477 15420986524006478275158277)
              ·
                refine ⟨2891434973251214676592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15420986524006478275158277 2891434973251214676592177)
                ·
                  refine ⟨2168576229938411007444133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891434973251214676592177 2168576229938411007444133)
                  ·
                    refine ⟨406608043113452063895775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168576229938411007444133 406608043113452063895775)
                    ·
                      rfl

theorem cell23_2375599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_2375599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375599 prefixEnd_2375599 := by exact prefixLift 2375599
  have htrace : WordTrace (prefixWord ++ tailWord_2375599) baseStart_2375599 baseEnd_2375599 := by
    simpa [prefixWord, tailWord_2375599, baseEnd_2375599] using wordTrace_append hprefix tailTrace_2375599
  have hstable : (prefixWord ++ tailWord_2375599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375599).length < 2 ^ (prefixWord ++ tailWord_2375599).sum := by decide
  have hdescent : baseEnd_2375599 < baseStart_2375599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375609 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2375609 : Nat := 118140960795 + 2375609 * 2 ^ 59
def prefixEnd_2375609 : Nat := 4983230072969 + 3 ^ 40 * 2375609 * 2
def baseEnd_2375609 : Nat := 1219829264146901152562279

theorem tailTrace_2375609 : CollatzResearch.WordTrace tailWord_2375609 prefixEnd_2375609 1219829264146901152562279 := by
  unfold tailWord_2375609
  simp only [CollatzResearch.WordTrace]
  refine ⟨86645578450581789561153881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57763718967054526374102587 86645578450581789561153881)
  ·
    refine ⟨64984183837936342170865411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86645578450581789561153881 64984183837936342170865411)
    ·
      refine ⟨97476275756904513256298117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64984183837936342170865411 97476275756904513256298117)
      ·
        refine ⟨18276801704419596235555897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97476275756904513256298117 18276801704419596235555897)
        ·
          refine ⟨13707601278314697176666923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18276801704419596235555897 13707601278314697176666923)
          ·
            refine ⟨20561401917472045765000385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13707601278314697176666923 20561401917472045765000385)
            ·
              refine ⟨15421051438104034323750289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20561401917472045765000385 15421051438104034323750289)
              ·
                refine ⟨11565788578578025742812717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15421051438104034323750289 11565788578578025742812717)
                ·
                  refine ⟨4337170716966759653554769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11565788578578025742812717 4337170716966759653554769)
                  ·
                    refine ⟨3252878037725069740166077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337170716966759653554769 3252878037725069740166077)
                    ·
                      refine ⟨1219829264146901152562279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252878037725069740166077 1219829264146901152562279)
                      ·
                        rfl

theorem cell23_2375609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2375609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375609 prefixEnd_2375609 := by exact prefixLift 2375609
  have htrace : WordTrace (prefixWord ++ tailWord_2375609) baseStart_2375609 baseEnd_2375609 := by
    simpa [prefixWord, tailWord_2375609, baseEnd_2375609] using wordTrace_append hprefix tailTrace_2375609
  have hstable : (prefixWord ++ tailWord_2375609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375609).length < 2 ^ (prefixWord ++ tailWord_2375609).sum := by decide
  have hdescent : baseEnd_2375609 < baseStart_2375609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375626 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_2375626 : Nat := 118140960795 + 2375626 * 2 ^ 59
def prefixEnd_2375626 : Nat := 4983230072969 + 3 ^ 40 * 2375626 * 2
def baseEnd_2375626 : Nat := 1219837993318027586049701

theorem tailTrace_2375626 : CollatzResearch.WordTrace tailWord_2375626 prefixEnd_2375626 1219837993318027586049701 := by
  unfold tailWord_2375626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661549622880050366130683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57764132327680134309681821 21661549622880050366130683)
  ·
    refine ⟨32492324434320075549196025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21661549622880050366130683 32492324434320075549196025)
    ·
      refine ⟨24369243325740056661897019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32492324434320075549196025 24369243325740056661897019)
      ·
        refine ⟨36553864988610084992845529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24369243325740056661897019 36553864988610084992845529)
        ·
          refine ⟨27415398741457563744634147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36553864988610084992845529 27415398741457563744634147)
          ·
            refine ⟨41123098112186345616951221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27415398741457563744634147 41123098112186345616951221)
            ·
              refine ⟨3855290448017469901589177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41123098112186345616951221 3855290448017469901589177)
              ·
                refine ⟨2891467836013102426191883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855290448017469901589177 2891467836013102426191883)
                ·
                  refine ⟨4337201754019653639287825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891467836013102426191883 4337201754019653639287825)
                  ·
                    refine ⟨3252901315514740229465869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337201754019653639287825 3252901315514740229465869)
                    ·
                      refine ⟨1219837993318027586049701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252901315514740229465869 1219837993318027586049701)
                      ·
                        rfl

theorem cell23_2375626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_2375626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375626 prefixEnd_2375626 := by exact prefixLift 2375626
  have htrace : WordTrace (prefixWord ++ tailWord_2375626) baseStart_2375626 baseEnd_2375626 := by
    simpa [prefixWord, tailWord_2375626, baseEnd_2375626] using wordTrace_append hprefix tailTrace_2375626
  have hstable : (prefixWord ++ tailWord_2375626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375626).length < 2 ^ (prefixWord ++ tailWord_2375626).sum := by decide
  have hdescent : baseEnd_2375626 < baseStart_2375626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375639 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2375639 : Nat := 118140960795 + 2375639 * 2 ^ 59
def prefixEnd_2375639 : Nat := 4983230072969 + 3 ^ 40 * 2375639 * 2
def baseEnd_2375639 : Nat := 1219844668566536035187141

theorem tailTrace_2375639 : CollatzResearch.WordTrace tailWord_2375639 prefixEnd_2375639 1219844668566536035187141 := by
  unfold tailWord_2375639
  simp only [CollatzResearch.WordTrace]
  refine ⟨86646672640473104684745971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57764448426982069789830647 86646672640473104684745971)
  ·
    refine ⟨129970008960709657027118957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86646672640473104684745971 129970008960709657027118957)
    ·
      refine ⟨48738753360266121385169609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129970008960709657027118957 48738753360266121385169609)
      ·
        refine ⟨36554065020199591038877207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48738753360266121385169609 36554065020199591038877207)
        ·
          refine ⟨54831097530299386558315811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36554065020199591038877207 54831097530299386558315811)
          ·
            refine ⟨82246646295449079837473717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54831097530299386558315811 82246646295449079837473717)
            ·
              refine ⟨7710623090198351234763161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82246646295449079837473717 7710623090198351234763161)
              ·
                refine ⟨5782967317648763426072371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7710623090198351234763161 5782967317648763426072371)
                ·
                  refine ⟨8674450976473145139108557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782967317648763426072371 8674450976473145139108557)
                  ·
                    refine ⟨3252919116177429427165709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8674450976473145139108557 3252919116177429427165709)
                    ·
                      refine ⟨1219844668566536035187141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3252919116177429427165709 1219844668566536035187141)
                      ·
                        rfl

theorem cell23_2375639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2375639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375639 prefixEnd_2375639 := by exact prefixLift 2375639
  have htrace : WordTrace (prefixWord ++ tailWord_2375639) baseStart_2375639 baseEnd_2375639 := by
    simpa [prefixWord, tailWord_2375639, baseEnd_2375639] using wordTrace_append hprefix tailTrace_2375639
  have hstable : (prefixWord ++ tailWord_2375639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375639).length < 2 ^ (prefixWord ++ tailWord_2375639).sum := by decide
  have hdescent : baseEnd_2375639 < baseStart_2375639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375650 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2375650 : Nat := 118140960795 + 2375650 * 2 ^ 59
def prefixEnd_2375650 : Nat := 4983230072969 + 3 ^ 40 * 2375650 * 2
def baseEnd_2375650 : Nat := 406616772284578497383197

theorem tailTrace_2375650 : CollatzResearch.WordTrace tailWord_2375650 prefixEnd_2375650 406616772284578497383197 := by
  unfold tailWord_2375650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661768460858313390849101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57764715895622169042264269 21661768460858313390849101)
  ·
    refine ⟨8123163172821867521568413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21661768460858313390849101 8123163172821867521568413)
    ·
      refine ⟨3046186189808200320588155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8123163172821867521568413 3046186189808200320588155)
      ·
        refine ⟨4569279284712300480882233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046186189808200320588155 4569279284712300480882233)
        ·
          refine ⟨3426959463534225360661675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4569279284712300480882233 3426959463534225360661675)
          ·
            refine ⟨5140439195301338040992513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426959463534225360661675 5140439195301338040992513)
            ·
              refine ⟨3855329396476003530744385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140439195301338040992513 3855329396476003530744385)
              ·
                refine ⟨2891497047357002648058289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855329396476003530744385 2891497047357002648058289)
                ·
                  refine ⟨2168622785517751986043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891497047357002648058289 2168622785517751986043717)
                  ·
                    refine ⟨406616772284578497383197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168622785517751986043717 406616772284578497383197)
                    ·
                      rfl

theorem cell23_2375650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2375650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375650 prefixEnd_2375650 := by exact prefixLift 2375650
  have htrace : WordTrace (prefixWord ++ tailWord_2375650) baseStart_2375650 baseEnd_2375650 := by
    simpa [prefixWord, tailWord_2375650, baseEnd_2375650] using wordTrace_append hprefix tailTrace_2375650
  have hstable : (prefixWord ++ tailWord_2375650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375650).length < 2 ^ (prefixWord ++ tailWord_2375650).sum := by decide
  have hdescent : baseEnd_2375650 < baseStart_2375650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375672 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_2375672 : Nat := 118140960795 + 2375672 * 2 ^ 59
def prefixEnd_2375672 : Nat := 4983230072969 + 3 ^ 40 * 2375672 * 2
def baseEnd_2375672 : Nat := 406620537809378135358163

theorem tailTrace_2375672 : CollatzResearch.WordTrace tailWord_2375672 prefixEnd_2375672 406620537809378135358163 := by
  unfold tailWord_2375672
  simp only [CollatzResearch.WordTrace]
  refine ⟨43323938124676775660348635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57765250832902367547131513 43323938124676775660348635)
  ·
    refine ⟨64985907187015163490522953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43323938124676775660348635 64985907187015163490522953)
    ·
      refine ⟨48739430390261372617892215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64985907187015163490522953 48739430390261372617892215)
      ·
        refine ⟨73109145585392058926838323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48739430390261372617892215 73109145585392058926838323)
        ·
          refine ⟨109663718378088088390257485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73109145585392058926838323 109663718378088088390257485)
          ·
            refine ⟨41123894391783033146346557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109663718378088088390257485 41123894391783033146346557)
            ·
              refine ⟨15421460396918637429879959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41123894391783033146346557 15421460396918637429879959)
              ·
                refine ⟨23132190595377956144819939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15421460396918637429879959 23132190595377956144819939)
                ·
                  refine ⟨34698285893066934217229909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23132190595377956144819939 34698285893066934217229909)
                  ·
                    refine ⟨406620537809378135358163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34698285893066934217229909 406620537809378135358163)
                    ·
                      rfl

theorem cell23_2375672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_2375672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375672 prefixEnd_2375672 := by exact prefixLift 2375672
  have htrace : WordTrace (prefixWord ++ tailWord_2375672) baseStart_2375672 baseEnd_2375672 := by
    simpa [prefixWord, tailWord_2375672, baseEnd_2375672] using wordTrace_append hprefix tailTrace_2375672
  have hstable : (prefixWord ++ tailWord_2375672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375672).length < 2 ^ (prefixWord ++ tailWord_2375672).sum := by decide
  have hdescent : baseEnd_2375672 < baseStart_2375672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375696 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2]
def baseStart_2375696 : Nat := 118140960795 + 2375696 * 2 ^ 59
def prefixEnd_2375696 : Nat := 4983230072969 + 3 ^ 40 * 2375696 * 2
def baseEnd_2375696 : Nat := 1219873936963842312174379

theorem tailTrace_2375696 : CollatzResearch.WordTrace tailWord_2375696 prefixEnd_2375696 1219873936963842312174379 := by
  unfold tailWord_2375696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43324375800633301709785471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57765834400844402279713961 43324375800633301709785471)
  ·
    refine ⟨64986563700949952564678207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43324375800633301709785471 64986563700949952564678207)
    ·
      refine ⟨97479845551424928847017311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64986563700949952564678207 97479845551424928847017311)
      ·
        refine ⟨146219768327137393270525967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97479845551424928847017311 146219768327137393270525967)
        ·
          refine ⟨219329652490706089905788951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146219768327137393270525967 219329652490706089905788951)
          ·
            refine ⟨328994478736059134858683427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219329652490706089905788951 328994478736059134858683427)
            ·
              refine ⟨493491718104088702288025141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328994478736059134858683427 493491718104088702288025141)
              ·
                refine ⟨46264848572258315839502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 493491718104088702288025141 46264848572258315839502357)
                ·
                  refine ⟨2168664776824608554976673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46264848572258315839502357 2168664776824608554976673)
                  ·
                    refine ⟨1626498582618456416232505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168664776824608554976673 1626498582618456416232505)
                    ·
                      refine ⟨1219873936963842312174379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626498582618456416232505 1219873936963842312174379)
                      ·
                        rfl

theorem cell23_2375696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2].length) (baseStart_2375696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375696 prefixEnd_2375696 := by exact prefixLift 2375696
  have htrace : WordTrace (prefixWord ++ tailWord_2375696) baseStart_2375696 baseEnd_2375696 := by
    simpa [prefixWord, tailWord_2375696, baseEnd_2375696] using wordTrace_append hprefix tailTrace_2375696
  have hstable : (prefixWord ++ tailWord_2375696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375696).length < 2 ^ (prefixWord ++ tailWord_2375696).sum := by decide
  have hdescent : baseEnd_2375696 < baseStart_2375696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375726 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2375726 : Nat := 118140960795 + 2375726 * 2 ^ 59
def prefixEnd_2375726 : Nat := 4983230072969 + 3 ^ 40 * 2375726 * 2
def baseEnd_2375726 : Nat := 1219889341383477194799241

theorem tailTrace_2375726 : CollatzResearch.WordTrace tailWord_2375726 prefixEnd_2375726 1219889341383477194799241 := by
  unfold tailWord_2375726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831230723894739817895379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57766563860771945695442021 10831230723894739817895379)
  ·
    refine ⟨16246846085842109726843069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831230723894739817895379 16246846085842109726843069)
    ·
      refine ⟨6092567282190791147566151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16246846085842109726843069 6092567282190791147566151)
      ·
        refine ⟨9138850923286186721349227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092567282190791147566151 9138850923286186721349227)
        ·
          refine ⟨13708276384929280082023841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138850923286186721349227 13708276384929280082023841)
          ·
            refine ⟨10281207288696960061517881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13708276384929280082023841 10281207288696960061517881)
            ·
              refine ⟨7710905466522720046138411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10281207288696960061517881 7710905466522720046138411)
              ·
                refine ⟨11566358199784080069207617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710905466522720046138411 11566358199784080069207617)
                ·
                  refine ⟨8674768649838060051905713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11566358199784080069207617 8674768649838060051905713)
                  ·
                    refine ⟨6506076487378545038929285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8674768649838060051905713 6506076487378545038929285)
                    ·
                      refine ⟨1219889341383477194799241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6506076487378545038929285 1219889341383477194799241)
                      ·
                        rfl

theorem cell23_2375726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2375726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375726 prefixEnd_2375726 := by exact prefixLift 2375726
  have htrace : WordTrace (prefixWord ++ tailWord_2375726) baseStart_2375726 baseEnd_2375726 := by
    simpa [prefixWord, tailWord_2375726, baseEnd_2375726] using wordTrace_append hprefix tailTrace_2375726
  have hstable : (prefixWord ++ tailWord_2375726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375726).length < 2 ^ (prefixWord ++ tailWord_2375726).sum := by decide
  have hdescent : baseEnd_2375726 < baseStart_2375726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375749 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_2375749 : Nat := 118140960795 + 2375749 * 2 ^ 59
def prefixEnd_2375749 : Nat := 4983230072969 + 3 ^ 40 * 2375749 * 2
def baseEnd_2375749 : Nat := 406633717146176868270545

theorem tailTrace_2375749 : CollatzResearch.WordTrace tailWord_2375749 prefixEnd_2375749 406633717146176868270545 := by
  unfold tailWord_2375749
  simp only [CollatzResearch.WordTrace]
  refine ⟨86650684670074593471250301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57767123113383062314166867 86650684670074593471250301)
  ·
    refine ⟨32494006751277972551718863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86650684670074593471250301 32494006751277972551718863)
    ·
      refine ⟨48741010126916958827578295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32494006751277972551718863 48741010126916958827578295)
      ·
        refine ⟨73111515190375438241367443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48741010126916958827578295 73111515190375438241367443)
        ·
          refine ⟨109667272785563157362051165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73111515190375438241367443 109667272785563157362051165)
          ·
            refine ⟨41125227294586184010769187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109667272785563157362051165 41125227294586184010769187)
            ·
              refine ⟨61687840941879276016153781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41125227294586184010769187 61687840941879276016153781)
              ·
                refine ⟨5783235088301182126514417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61687840941879276016153781 5783235088301182126514417)
                ·
                  refine ⟨4337426316225886594885813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783235088301182126514417 4337426316225886594885813)
                  ·
                    refine ⟨406633717146176868270545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4337426316225886594885813 406633717146176868270545)
                    ·
                      rfl

theorem cell23_2375749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_2375749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375749 prefixEnd_2375749 := by exact prefixLift 2375749
  have htrace : WordTrace (prefixWord ++ tailWord_2375749) baseStart_2375749 baseEnd_2375749 := by
    simpa [prefixWord, tailWord_2375749, baseEnd_2375749] using wordTrace_append hprefix tailTrace_2375749
  have hstable : (prefixWord ++ tailWord_2375749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375749).length < 2 ^ (prefixWord ++ tailWord_2375749).sum := by decide
  have hdescent : baseEnd_2375749 < baseStart_2375749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375829 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2375829 : Nat := 118140960795 + 2375829 * 2 ^ 59
def prefixEnd_2375829 : Nat := 4983230072969 + 3 ^ 40 * 2375829 * 2
def baseEnd_2375829 : Nat := 1219942229890890291811267

theorem tailTrace_2375829 : CollatzResearch.WordTrace tailWord_2375829 prefixEnd_2375829 1219942229890890291811267 := by
  unfold tailWord_2375829
  simp only [CollatzResearch.WordTrace]
  refine ⟨86653602509784767134162541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57769068339856511422775027 86653602509784767134162541)
  ·
    refine ⟨32495100941169287675310953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86653602509784767134162541 32495100941169287675310953)
    ·
      refine ⟨24371325705876965756483215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32495100941169287675310953 24371325705876965756483215)
      ·
        refine ⟨36556988558815448634724823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24371325705876965756483215 36556988558815448634724823)
        ·
          refine ⟨54835482838223172952087235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36556988558815448634724823 54835482838223172952087235)
          ·
            refine ⟨82253224257334759428130853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54835482838223172952087235 82253224257334759428130853)
            ·
              refine ⟨15422479548250267392774535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82253224257334759428130853 15422479548250267392774535)
              ·
                refine ⟨23133719322375401089161803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15422479548250267392774535 23133719322375401089161803)
                ·
                  refine ⟨34700578983563101633742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23133719322375401089161803 34700578983563101633742705)
                  ·
                    refine ⟨26025434237672326225307029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34700578983563101633742705 26025434237672326225307029)
                    ·
                      refine ⟨1219942229890890291811267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26025434237672326225307029 1219942229890890291811267)
                      ·
                        rfl

theorem cell23_2375829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2375829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375829 prefixEnd_2375829 := by exact prefixLift 2375829
  have htrace : WordTrace (prefixWord ++ tailWord_2375829) baseStart_2375829 baseEnd_2375829 := by
    simpa [prefixWord, tailWord_2375829, baseEnd_2375829] using wordTrace_append hprefix tailTrace_2375829
  have hstable : (prefixWord ++ tailWord_2375829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375829).length < 2 ^ (prefixWord ++ tailWord_2375829).sum := by decide
  have hdescent : baseEnd_2375829 < baseStart_2375829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375854 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2375854 : Nat := 118140960795 + 2375854 * 2 ^ 59
def prefixEnd_2375854 : Nat := 4983230072969 + 3 ^ 40 * 2375854 * 2
def baseEnd_2375854 : Nat := 1219955066907252693998653

theorem tailTrace_2375854 : CollatzResearch.WordTrace tailWord_2375854 prefixEnd_2375854 1219955066907252693998653 := by
  unfold tailWord_2375854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831814291836774550477827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57769676223129464269215077 10831814291836774550477827)
  ·
    refine ⟨16247721437755161825716741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831814291836774550477827 16247721437755161825716741)
    ·
      refine ⟨3046447769579092842321889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16247721437755161825716741 3046447769579092842321889)
      ·
        refine ⟨2284835827184319631741417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3046447769579092842321889 2284835827184319631741417)
        ·
          refine ⟨1713626870388239723806063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284835827184319631741417 1713626870388239723806063)
          ·
            refine ⟨2570440305582359585709095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713626870388239723806063 2570440305582359585709095)
            ·
              refine ⟨3855660458373539378563643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570440305582359585709095 3855660458373539378563643)
              ·
                refine ⟨5783490687560309067845465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855660458373539378563643 5783490687560309067845465)
                ·
                  refine ⟨4337618015670231800884099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783490687560309067845465 4337618015670231800884099)
                  ·
                    refine ⟨6506427023505347701326149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4337618015670231800884099 6506427023505347701326149)
                    ·
                      refine ⟨1219955066907252693998653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6506427023505347701326149 1219955066907252693998653)
                      ·
                        rfl

theorem cell23_2375854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2375854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375854 prefixEnd_2375854 := by exact prefixLift 2375854
  have htrace : WordTrace (prefixWord ++ tailWord_2375854) baseStart_2375854 baseEnd_2375854 := by
    simpa [prefixWord, tailWord_2375854, baseEnd_2375854] using wordTrace_append hprefix tailTrace_2375854
  have hstable : (prefixWord ++ tailWord_2375854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375854).length < 2 ^ (prefixWord ++ tailWord_2375854).sum := by decide
  have hdescent : baseEnd_2375854 < baseStart_2375854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375857 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2375857 : Nat := 118140960795 + 2375857 * 2 ^ 59
def prefixEnd_2375857 : Nat := 4983230072969 + 3 ^ 40 * 2375857 * 2
def baseEnd_2375857 : Nat := 1219956607349216182261139

theorem tailTrace_2375857 : CollatzResearch.WordTrace tailWord_2375857 prefixEnd_2375857 1219956607349216182261139 := by
  unfold tailWord_2375857
  simp only [CollatzResearch.WordTrace]
  refine ⟨86654623753683327916181825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57769749169122218610787883 86654623753683327916181825)
  ·
    refine ⟨64990967815262495937136369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86654623753683327916181825 64990967815262495937136369)
    ·
      refine ⟨48743225861446871952852277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64990967815262495937136369 48743225861446871952852277)
      ·
        refine ⟨4569677424510644245579901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48743225861446871952852277 4569677424510644245579901)
        ·
          refine ⟨1713629034191491592092463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4569677424510644245579901 1713629034191491592092463)
          ·
            refine ⟨2570443551287237388138695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713629034191491592092463 2570443551287237388138695)
            ·
              refine ⟨3855665326930856082208043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570443551287237388138695 3855665326930856082208043)
              ·
                refine ⟨5783497990396284123312065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855665326930856082208043 5783497990396284123312065)
                ·
                  refine ⟨4337623492797213092484049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783497990396284123312065 4337623492797213092484049)
                  ·
                    refine ⟨3253217619597909819363037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4337623492797213092484049 3253217619597909819363037)
                    ·
                      refine ⟨1219956607349216182261139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3253217619597909819363037 1219956607349216182261139)
                      ·
                        rfl

theorem cell23_2375857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2375857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375857 prefixEnd_2375857 := by exact prefixLift 2375857
  have htrace : WordTrace (prefixWord ++ tailWord_2375857) baseStart_2375857 baseEnd_2375857 := by
    simpa [prefixWord, tailWord_2375857, baseEnd_2375857] using wordTrace_append hprefix tailTrace_2375857
  have hstable : (prefixWord ++ tailWord_2375857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375857).length < 2 ^ (prefixWord ++ tailWord_2375857).sum := by decide
  have hdescent : baseEnd_2375857 < baseStart_2375857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375863 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_2375863 : Nat := 118140960795 + 2375863 * 2 ^ 59
def prefixEnd_2375863 : Nat := 4983230072969 + 3 ^ 40 * 2375863 * 2
def baseEnd_2375863 : Nat := 1219959688233143158786111

theorem tailTrace_2375863 : CollatzResearch.WordTrace tailWord_2375863 prefixEnd_2375863 1219959688233143158786111 := by
  unfold tailWord_2375863
  simp only [CollatzResearch.WordTrace]
  refine ⟨86654842591661590940900243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57769895061107727293933495 86654842591661590940900243)
  ·
    refine ⟨129982263887492386411350365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86654842591661590940900243 129982263887492386411350365)
    ·
      refine ⟨48743348957809644904256387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129982263887492386411350365 48743348957809644904256387)
      ·
        refine ⟨73115023436714467356384581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48743348957809644904256387 73115023436714467356384581)
        ·
          refine ⟨13709066894383962629322109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73115023436714467356384581 13709066894383962629322109)
          ·
            refine ⟨5140900085393985985995791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13709066894383962629322109 5140900085393985985995791)
            ·
              refine ⟨7711350128090978978993687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140900085393985985995791 7711350128090978978993687)
              ·
                refine ⟨11567025192136468468490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711350128090978978993687 11567025192136468468490531)
                ·
                  refine ⟨17350537788204702702735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11567025192136468468490531 17350537788204702702735797)
                  ·
                    refine ⟨1626612917644190878381481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17350537788204702702735797 1626612917644190878381481)
                    ·
                      refine ⟨1219959688233143158786111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626612917644190878381481 1219959688233143158786111)
                      ·
                        rfl

theorem cell23_2375863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_2375863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375863 prefixEnd_2375863 := by exact prefixLift 2375863
  have htrace : WordTrace (prefixWord ++ tailWord_2375863) baseStart_2375863 baseEnd_2375863 := by
    simpa [prefixWord, tailWord_2375863, baseEnd_2375863] using wordTrace_append hprefix tailTrace_2375863
  have hstable : (prefixWord ++ tailWord_2375863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375863).length < 2 ^ (prefixWord ++ tailWord_2375863).sum := by decide
  have hdescent : baseEnd_2375863 < baseStart_2375863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375896 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2375896 : Nat := 118140960795 + 2375896 * 2 ^ 59
def prefixEnd_2375896 : Nat := 4983230072969 + 3 ^ 40 * 2375896 * 2
def baseEnd_2375896 : Nat := 1219976633094741529673459

theorem tailTrace_2375896 : CollatzResearch.WordTrace tailWord_2375896 prefixEnd_2375896 1219976633094741529673459 := by
  unfold tailWord_2375896
  simp only [CollatzResearch.WordTrace]
  refine ⟨43328023100271018788425771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57770697467028025051234361 43328023100271018788425771)
  ·
    refine ⟨64992034650406528182638657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43328023100271018788425771 64992034650406528182638657)
    ·
      refine ⟨48744025987804896136978993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64992034650406528182638657 48744025987804896136978993)
      ·
        refine ⟨36558019490853672102734245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48744025987804896136978993 36558019490853672102734245)
        ·
          refine ⟨6854628654535063519262671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36558019490853672102734245 6854628654535063519262671)
          ·
            refine ⟨10281942981802595278894007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6854628654535063519262671 10281942981802595278894007)
            ·
              refine ⟨15422914472703892918341011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10281942981802595278894007 15422914472703892918341011)
              ·
                refine ⟨23134371709055839377511517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15422914472703892918341011 23134371709055839377511517)
                ·
                  refine ⟨8675389390895939766566819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23134371709055839377511517 8675389390895939766566819)
                  ·
                    refine ⟨13013084086343909649850229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8675389390895939766566819 13013084086343909649850229)
                    ·
                      refine ⟨1219976633094741529673459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13013084086343909649850229 1219976633094741529673459)
                      ·
                        rfl

theorem cell23_2375896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2375896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375896 prefixEnd_2375896 := by exact prefixLift 2375896
  have htrace : WordTrace (prefixWord ++ tailWord_2375896) baseStart_2375896 baseEnd_2375896 := by
    simpa [prefixWord, tailWord_2375896, baseEnd_2375896] using wordTrace_append hprefix tailTrace_2375896
  have hstable : (prefixWord ++ tailWord_2375896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375896).length < 2 ^ (prefixWord ++ tailWord_2375896).sum := by decide
  have hdescent : baseEnd_2375896 < baseStart_2375896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375960 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2375960 : Nat := 118140960795 + 2375960 * 2 ^ 59
def prefixEnd_2375960 : Nat := 4983230072969 + 3 ^ 40 * 2375960 * 2
def baseEnd_2375960 : Nat := 1220009495856629279273165

theorem tailTrace_2375960 : CollatzResearch.WordTrace tailWord_2375960 prefixEnd_2375960 1220009495856629279273165 := by
  unfold tailWord_2375960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43329190236155088253590667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57772253648206784338120889 43329190236155088253590667)
  ·
    refine ⟨64993785354232632380386001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43329190236155088253590667 64993785354232632380386001)
    ·
      refine ⟨48745339015674474285289501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64993785354232632380386001 48745339015674474285289501)
      ·
        refine ⟨18279502130877927856983563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48745339015674474285289501 18279502130877927856983563)
        ·
          refine ⟨27419253196316891785475345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18279502130877927856983563 27419253196316891785475345)
          ·
            refine ⟨20564439897237668839106509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27419253196316891785475345 20564439897237668839106509)
            ·
              refine ⟨7711664961464125814664941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20564439897237668839106509 7711664961464125814664941)
              ·
                refine ⟨2891874360549047180499353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7711664961464125814664941 2891874360549047180499353)
                ·
                  refine ⟨2168905770411785385374515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891874360549047180499353 2168905770411785385374515)
                  ·
                    refine ⟨3253358655617678078061773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2168905770411785385374515 3253358655617678078061773)
                    ·
                      refine ⟨1220009495856629279273165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3253358655617678078061773 1220009495856629279273165)
                      ·
                        rfl

theorem cell23_2375960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2375960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375960 prefixEnd_2375960 := by exact prefixLift 2375960
  have htrace : WordTrace (prefixWord ++ tailWord_2375960) baseStart_2375960 baseEnd_2375960 := by
    simpa [prefixWord, tailWord_2375960, baseEnd_2375960] using wordTrace_append hprefix tailTrace_2375960
  have hstable : (prefixWord ++ tailWord_2375960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375960).length < 2 ^ (prefixWord ++ tailWord_2375960).sum := by decide
  have hdescent : baseEnd_2375960 < baseStart_2375960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375983 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 4, 2]
def baseStart_2375983 : Nat := 118140960795 + 2375983 * 2 ^ 59
def prefixEnd_2375983 : Nat := 4983230072969 + 3 ^ 40 * 2375983 * 2
def baseEnd_2375983 : Nat := 1220021305911682689285559

theorem tailTrace_2375983 : CollatzResearch.WordTrace tailWord_2375983 prefixEnd_2375983 1220021305911682689285559 := by
  unfold tailWord_2375983
  simp only [CollatzResearch.WordTrace]
  refine ⟨86659219351226851435268603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57772812900817900956845735 86659219351226851435268603)
  ·
    refine ⟨129988829026840277152902905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86659219351226851435268603 129988829026840277152902905)
    ·
      refine ⟨97491621770130207864677179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129988829026840277152902905 97491621770130207864677179)
      ·
        refine ⟨146237432655195311797015769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97491621770130207864677179 146237432655195311797015769)
        ·
          refine ⟨109678074491396483847761827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146237432655195311797015769 109678074491396483847761827)
          ·
            refine ⟨164517111737094725771642741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109678074491396483847761827 164517111737094725771642741)
            ·
              refine ⟨15423479225352630541091507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164517111737094725771642741 15423479225352630541091507)
              ·
                refine ⟨23135218838028945811637261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15423479225352630541091507 23135218838028945811637261)
                ·
                  refine ⟨8675707064260854679363973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23135218838028945811637261 8675707064260854679363973)
                  ·
                    refine ⟨1626695074548910252380745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8675707064260854679363973 1626695074548910252380745)
                    ·
                      refine ⟨1220021305911682689285559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626695074548910252380745 1220021305911682689285559)
                      ·
                        rfl

theorem cell23_2375983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4, 2].length) (baseStart_2375983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375983 prefixEnd_2375983 := by exact prefixLift 2375983
  have htrace : WordTrace (prefixWord ++ tailWord_2375983) baseStart_2375983 baseEnd_2375983 := by
    simpa [prefixWord, tailWord_2375983, baseEnd_2375983] using wordTrace_append hprefix tailTrace_2375983
  have hstable : (prefixWord ++ tailWord_2375983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375983).length < 2 ^ (prefixWord ++ tailWord_2375983).sum := by decide
  have hdescent : baseEnd_2375983 < baseStart_2375983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375987 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 1, 3, 2]
def baseStart_2375987 : Nat := 118140960795 + 2375987 * 2 ^ 59
def prefixEnd_2375987 : Nat := 4983230072969 + 3 ^ 40 * 2375987 * 2
def baseEnd_2375987 : Nat := 1220023359834300673635541

theorem tailTrace_2375987 : CollatzResearch.WordTrace tailWord_2375987 prefixEnd_2375987 1220023359834300673635541 := by
  unfold tailWord_2375987
  simp only [CollatzResearch.WordTrace]
  refine ⟨86659365243212360118414215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57772910162141573412276143 86659365243212360118414215)
  ·
    refine ⟨129989047864818540177621323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86659365243212360118414215 129989047864818540177621323)
    ·
      refine ⟨194983571797227810266431985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129989047864818540177621323 194983571797227810266431985)
      ·
        refine ⟨146237678847920857699823989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194983571797227810266431985 146237678847920857699823989)
        ·
          refine ⟨13709782391992580409358499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146237678847920857699823989 13709782391992580409358499)
          ·
            refine ⟨20564673587988870614037749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13709782391992580409358499 20564673587988870614037749)
            ·
              refine ⟨1927938148873956620066039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20564673587988870614037749 1927938148873956620066039)
              ·
                refine ⟨2891907223310934930099059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927938148873956620066039 2891907223310934930099059)
                ·
                  refine ⟨4337860834966402395148589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891907223310934930099059 4337860834966402395148589)
                  ·
                    refine ⟨1626697813112400898180721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4337860834966402395148589 1626697813112400898180721)
                    ·
                      refine ⟨1220023359834300673635541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626697813112400898180721 1220023359834300673635541)
                      ·
                        rfl

theorem cell23_2375987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 3, 2].length) (baseStart_2375987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2375987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2375987 prefixEnd_2375987 := by exact prefixLift 2375987
  have htrace : WordTrace (prefixWord ++ tailWord_2375987) baseStart_2375987 baseEnd_2375987 := by
    simpa [prefixWord, tailWord_2375987, baseEnd_2375987] using wordTrace_append hprefix tailTrace_2375987
  have hstable : (prefixWord ++ tailWord_2375987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375987).length < 2 ^ (prefixWord ++ tailWord_2375987).sum := by decide
  have hdescent : baseEnd_2375987 < baseStart_2375987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376017 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_2376017 : Nat := 118140960795 + 2376017 * 2 ^ 59
def prefixEnd_2376017 : Nat := 4983230072969 + 3 ^ 40 * 2376017 * 2
def baseEnd_2376017 : Nat := 1220038764253935556260403

theorem tailTrace_2376017 : CollatzResearch.WordTrace tailWord_2376017 prefixEnd_2376017 1220038764253935556260403 := by
  unfold tailWord_2376017
  simp only [CollatzResearch.WordTrace]
  refine ⟨86660459433103675242006305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57773639622069116828004203 86660459433103675242006305)
  ·
    refine ⟨64995344574827756431504729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86660459433103675242006305 64995344574827756431504729)
    ·
      refine ⟨48746508431120817323628547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64995344574827756431504729 48746508431120817323628547)
      ·
        refine ⟨73119762646681225985442821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48746508431120817323628547 73119762646681225985442821)
        ·
          refine ⟨13709955496252729872270529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73119762646681225985442821 13709955496252729872270529)
          ·
            refine ⟨10282466622189547404202897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13709955496252729872270529 10282466622189547404202897)
            ·
              refine ⟨7711849966642160553152173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10282466622189547404202897 7711849966642160553152173)
              ·
                refine ⟨2891943737490810207432065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7711849966642160553152173 2891943737490810207432065)
                ·
                  refine ⟨2168957803118107655574049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891943737490810207432065 2168957803118107655574049)
                  ·
                    refine ⟨1626718352338580741680537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168957803118107655574049 1626718352338580741680537)
                    ·
                      refine ⟨1220038764253935556260403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626718352338580741680537 1220038764253935556260403)
                      ·
                        rfl

theorem cell23_2376017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_2376017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376017 prefixEnd_2376017 := by exact prefixLift 2376017
  have htrace : WordTrace (prefixWord ++ tailWord_2376017) baseStart_2376017 baseEnd_2376017 := by
    simpa [prefixWord, tailWord_2376017, baseEnd_2376017] using wordTrace_append hprefix tailTrace_2376017
  have hstable : (prefixWord ++ tailWord_2376017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376017).length < 2 ^ (prefixWord ++ tailWord_2376017).sum := by decide
  have hdescent : baseEnd_2376017 < baseStart_2376017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376040 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 5]
def baseStart_2376040 : Nat := 118140960795 + 2376040 * 2 ^ 59
def prefixEnd_2376040 : Nat := 4983230072969 + 3 ^ 40 * 2376040 * 2
def baseEnd_2376040 : Nat := 135561174923220996252533

theorem tailTrace_2376040 : CollatzResearch.WordTrace tailWord_2376040 prefixEnd_2376040 135561174923220996252533 := by
  unfold tailWord_2376040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43330649156010175085046787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57774198874680233446729049 43330649156010175085046787)
  ·
    refine ⟨64995973734015262627570181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43330649156010175085046787 64995973734015262627570181)
    ·
      refine ⟨12186745075127861742669409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64995973734015262627570181 12186745075127861742669409)
      ·
        refine ⟨9140058806345896307002057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12186745075127861742669409 9140058806345896307002057)
        ·
          refine ⟨6855044104759422230251543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9140058806345896307002057 6855044104759422230251543)
          ·
            refine ⟨10282566157139133345377315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855044104759422230251543 10282566157139133345377315)
            ·
              refine ⟨15423849235708700018065973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10282566157139133345377315 15423849235708700018065973)
              ·
                refine ⟨1445985865847690626693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15423849235708700018065973 1445985865847690626693685)
                ·
                  refine ⟨135561174923220996252533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1445985865847690626693685 135561174923220996252533)
                  ·
                    rfl

theorem cell23_2376040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 5].length) (baseStart_2376040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376040 prefixEnd_2376040 := by exact prefixLift 2376040
  have htrace : WordTrace (prefixWord ++ tailWord_2376040) baseStart_2376040 baseEnd_2376040 := by
    simpa [prefixWord, tailWord_2376040, baseEnd_2376040] using wordTrace_append hprefix tailTrace_2376040
  have hstable : (prefixWord ++ tailWord_2376040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376040).length < 2 ^ (prefixWord ++ tailWord_2376040).sum := by decide
  have hdescent : baseEnd_2376040 < baseStart_2376040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376043 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 5, 2]
def baseStart_2376043 : Nat := 118140960795 + 2376043 * 2 ^ 59
def prefixEnd_2376043 : Nat := 4983230072969 + 3 ^ 40 * 2376043 * 2
def baseEnd_2376043 : Nat := 1220052114750952454535283

theorem tailTrace_2376043 : CollatzResearch.WordTrace tailWord_2376043 prefixEnd_2376043 1220052114750952454535283 := by
  unfold tailWord_2376043
  simp only [CollatzResearch.WordTrace]
  refine ⟨86661407731009481682452783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57774271820672987788301855 86661407731009481682452783)
  ·
    refine ⟨129992111596514222523679175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86661407731009481682452783 129992111596514222523679175)
    ·
      refine ⟨194988167394771333785518763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129992111596514222523679175 194988167394771333785518763)
      ·
        refine ⟨292482251092157000678278145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194988167394771333785518763 292482251092157000678278145)
        ·
          refine ⟨219361688319117750508708609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292482251092157000678278145 219361688319117750508708609)
          ·
            refine ⟨164521266239338312881531457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219361688319117750508708609 164521266239338312881531457)
            ·
              refine ⟨123390949679503734661148593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164521266239338312881531457 123390949679503734661148593)
              ·
                refine ⟨92543212259627800995861445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123390949679503734661148593 92543212259627800995861445)
                ·
                  refine ⟨17351852298680212686724021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92543212259627800995861445 17351852298680212686724021)
                  ·
                    refine ⟨1626736153001269939380377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17351852298680212686724021 1626736153001269939380377)
                    ·
                      refine ⟨1220052114750952454535283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626736153001269939380377 1220052114750952454535283)
                      ·
                        rfl

theorem cell23_2376043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5, 2].length) (baseStart_2376043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376043 prefixEnd_2376043 := by exact prefixLift 2376043
  have htrace : WordTrace (prefixWord ++ tailWord_2376043) baseStart_2376043 baseEnd_2376043 := by
    simpa [prefixWord, tailWord_2376043, baseEnd_2376043] using wordTrace_append hprefix tailTrace_2376043
  have hstable : (prefixWord ++ tailWord_2376043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376043).length < 2 ^ (prefixWord ++ tailWord_2376043).sum := by decide
  have hdescent : baseEnd_2376043 < baseStart_2376043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376073 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_2376073 : Nat := 118140960795 + 2376073 * 2 ^ 59
def prefixEnd_2376073 : Nat := 4983230072969 + 3 ^ 40 * 2376073 * 2
def baseEnd_2376073 : Nat := 1220067519170587337160145

theorem tailTrace_2376073 : CollatzResearch.WordTrace tailWord_2376073 prefixEnd_2376073 1220067519170587337160145 := by
  unfold tailWord_2376073
  simp only [CollatzResearch.WordTrace]
  refine ⟨86662501920900796806044873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57775001280600531204029915 86662501920900796806044873)
  ·
    refine ⟨64996876440675597604533655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86662501920900796806044873 64996876440675597604533655)
    ·
      refine ⟨97495314661013396406800483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64996876440675597604533655 97495314661013396406800483)
      ·
        refine ⟨146242971991520094610200725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97495314661013396406800483 146242971991520094610200725)
        ·
          refine ⟨6855139312102504434853159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146242971991520094610200725 6855139312102504434853159)
          ·
            refine ⟨10282708968153756652279739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6855139312102504434853159 10282708968153756652279739)
            ·
              refine ⟨15424063452230634978419609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10282708968153756652279739 15424063452230634978419609)
              ·
                refine ⟨11568047589172976233814707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15424063452230634978419609 11568047589172976233814707)
                ·
                  refine ⟨17352071383759464350722061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11568047589172976233814707 17352071383759464350722061)
                  ·
                    refine ⟨6507026768909799131520773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17352071383759464350722061 6507026768909799131520773)
                    ·
                      refine ⟨1220067519170587337160145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6507026768909799131520773 1220067519170587337160145)
                      ·
                        rfl

theorem cell23_2376073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_2376073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376073 prefixEnd_2376073 := by exact prefixLift 2376073
  have htrace : WordTrace (prefixWord ++ tailWord_2376073) baseStart_2376073 baseEnd_2376073 := by
    simpa [prefixWord, tailWord_2376073, baseEnd_2376073] using wordTrace_append hprefix tailTrace_2376073
  have hstable : (prefixWord ++ tailWord_2376073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376073).length < 2 ^ (prefixWord ++ tailWord_2376073).sum := by decide
  have hdescent : baseEnd_2376073 < baseStart_2376073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376113 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 8]
def baseStart_2376113 : Nat := 118140960795 + 2376113 * 2 ^ 59
def prefixEnd_2376113 : Nat := 4983230072969 + 3 ^ 40 * 2376113 * 2
def baseEnd_2376113 : Nat := 135565339821863020073329

theorem tailTrace_2376113 : CollatzResearch.WordTrace tailWord_2376113 prefixEnd_2376113 135565339821863020073329 := by
  unfold tailWord_2376113
  simp only [CollatzResearch.WordTrace]
  refine ⟨86663960840755883637500993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57775973893837255758333995 86663960840755883637500993)
  ·
    refine ⟨64997970630566912728125745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86663960840755883637500993 64997970630566912728125745)
    ·
      refine ⟨48748477972925184546094309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64997970630566912728125745 48748477972925184546094309)
      ·
        refine ⟨9140339619923472102392683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48748477972925184546094309 9140339619923472102392683)
        ·
          refine ⟨13710509429885208153589025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140339619923472102392683 13710509429885208153589025)
          ·
            refine ⟨10282882072413906115191769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13710509429885208153589025 10282882072413906115191769)
            ·
              refine ⟨7712161554310429586393827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10282882072413906115191769 7712161554310429586393827)
              ·
                refine ⟨11568242331465644379590741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712161554310429586393827 11568242331465644379590741)
                ·
                  refine ⟨135565339821863020073329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11568242331465644379590741 135565339821863020073329)
                  ·
                    rfl

theorem cell23_2376113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_2376113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376113 prefixEnd_2376113 := by exact prefixLift 2376113
  have htrace : WordTrace (prefixWord ++ tailWord_2376113) baseStart_2376113 baseEnd_2376113 := by
    simpa [prefixWord, tailWord_2376113, baseEnd_2376113] using wordTrace_append hprefix tailTrace_2376113
  have hstable : (prefixWord ++ tailWord_2376113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376113).length < 2 ^ (prefixWord ++ tailWord_2376113).sum := by decide
  have hdescent : baseEnd_2376113 < baseStart_2376113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376167 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2376167 : Nat := 118140960795 + 2376167 * 2 ^ 59
def prefixEnd_2376167 : Nat := 4983230072969 + 3 ^ 40 * 2376167 * 2
def baseEnd_2376167 : Nat := 1220115786352109969384713

theorem tailTrace_2376167 : CollatzResearch.WordTrace tailWord_2376167 prefixEnd_2376167 1220115786352109969384713 := by
  unfold tailWord_2376167
  simp only [CollatzResearch.WordTrace]
  refine ⟨86665930382560250859966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57777286921706833906644503 86665930382560250859966755)
  ·
    refine ⟨129998895573840376289950133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86665930382560250859966755 129998895573840376289950133)
    ·
      refine ⟨12187396460047535277182825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129998895573840376289950133 12187396460047535277182825)
      ·
        refine ⟨9140547345035651457887119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12187396460047535277182825 9140547345035651457887119)
        ·
          refine ⟨13710821017553477186830679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140547345035651457887119 13710821017553477186830679)
          ·
            refine ⟨20566231526330215780246019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13710821017553477186830679 20566231526330215780246019)
            ·
              refine ⟨30849347289495323670369029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20566231526330215780246019 30849347289495323670369029)
              ·
                refine ⟨5784252616780373188194193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30849347289495323670369029 5784252616780373188194193)
                ·
                  refine ⟨4338189462585279891145645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784252616780373188194193 4338189462585279891145645)
                  ·
                    refine ⟨1626821048469479959179617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4338189462585279891145645 1626821048469479959179617)
                    ·
                      refine ⟨1220115786352109969384713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626821048469479959179617 1220115786352109969384713)
                      ·
                        rfl

theorem cell23_2376167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2376167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376167 prefixEnd_2376167 := by exact prefixLift 2376167
  have htrace : WordTrace (prefixWord ++ tailWord_2376167) baseStart_2376167 baseEnd_2376167 := by
    simpa [prefixWord, tailWord_2376167, baseEnd_2376167] using wordTrace_append hprefix tailTrace_2376167
  have hstable : (prefixWord ++ tailWord_2376167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376167).length < 2 ^ (prefixWord ++ tailWord_2376167).sum := by decide
  have hdescent : baseEnd_2376167 < baseStart_2376167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376197 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_2376197 : Nat := 118140960795 + 2376197 * 2 ^ 59
def prefixEnd_2376197 : Nat := 4983230072969 + 3 ^ 40 * 2376197 * 2
def baseEnd_2376197 : Nat := 1220131190771744852009575

theorem tailTrace_2376197 : CollatzResearch.WordTrace tailWord_2376197 prefixEnd_2376197 1220131190771744852009575 := by
  unfold tailWord_2376197
  simp only [CollatzResearch.WordTrace]
  refine ⟨86667024572451565983558845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57778016381634377322372563 86667024572451565983558845)
  ·
    refine ⟨32500134214669337243834567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86667024572451565983558845 32500134214669337243834567)
    ·
      refine ⟨48750201322004005865751851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32500134214669337243834567 48750201322004005865751851)
      ·
        refine ⟨73125301983006008798627777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48750201322004005865751851 73125301983006008798627777)
        ·
          refine ⟨54843976487254506598970833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73125301983006008798627777 54843976487254506598970833)
          ·
            refine ⟨41132982365440879949228125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54843976487254506598970833 41132982365440879949228125)
            ·
              refine ⟨15424868387040329980960547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41132982365440879949228125 15424868387040329980960547)
              ·
                refine ⟨23137302580560494971440821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15424868387040329980960547 23137302580560494971440821)
                ·
                  refine ⟨2169122116927546403572577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23137302580560494971440821 2169122116927546403572577)
                  ·
                    refine ⟨1626841587695659802679433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169122116927546403572577 1626841587695659802679433)
                    ·
                      refine ⟨1220131190771744852009575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626841587695659802679433 1220131190771744852009575)
                      ·
                        rfl

theorem cell23_2376197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_2376197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376197 prefixEnd_2376197 := by exact prefixLift 2376197
  have htrace : WordTrace (prefixWord ++ tailWord_2376197) baseStart_2376197 baseEnd_2376197 := by
    simpa [prefixWord, tailWord_2376197, baseEnd_2376197] using wordTrace_append hprefix tailTrace_2376197
  have hstable : (prefixWord ++ tailWord_2376197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376197).length < 2 ^ (prefixWord ++ tailWord_2376197).sum := by decide
  have hdescent : baseEnd_2376197 < baseStart_2376197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376223 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2376223 : Nat := 118140960795 + 2376223 * 2 ^ 59
def prefixEnd_2376223 : Nat := 4983230072969 + 3 ^ 40 * 2376223 * 2
def baseEnd_2376223 : Nat := 1220144541268761750284455

theorem tailTrace_2376223 : CollatzResearch.WordTrace tailWord_2376223 prefixEnd_2376223 1220144541268761750284455 := by
  unfold tailWord_2376223
  simp only [CollatzResearch.WordTrace]
  refine ⟨86667972870357372424005323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57778648580238248282670215 86667972870357372424005323)
  ·
    refine ⟨130001959305536058636007985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86667972870357372424005323 130001959305536058636007985)
    ·
      refine ⟨97501469479152043977005989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130001959305536058636007985 97501469479152043977005989)
      ·
        refine ⟨18281525527341008245688623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97501469479152043977005989 18281525527341008245688623)
        ·
          refine ⟨27422288291011512368532935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18281525527341008245688623 27422288291011512368532935)
          ·
            refine ⟨41133432436517268552799403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27422288291011512368532935 41133432436517268552799403)
            ·
              refine ⟨61700148654775902829199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41133432436517268552799403 61700148654775902829199105)
              ·
                refine ⟨46275111491081927121899329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61700148654775902829199105 46275111491081927121899329)
                ·
                  refine ⟨34706333618311445341424497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46275111491081927121899329 34706333618311445341424497)
                  ·
                    refine ⟨26029750213733584006068373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34706333618311445341424497 26029750213733584006068373)
                    ·
                      refine ⟨1220144541268761750284455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26029750213733584006068373 1220144541268761750284455)
                      ·
                        rfl

theorem cell23_2376223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2376223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376223 prefixEnd_2376223 := by exact prefixLift 2376223
  have htrace : WordTrace (prefixWord ++ tailWord_2376223) baseStart_2376223 baseEnd_2376223 := by
    simpa [prefixWord, tailWord_2376223, baseEnd_2376223] using wordTrace_append hprefix tailTrace_2376223
  have hstable : (prefixWord ++ tailWord_2376223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376223).length < 2 ^ (prefixWord ++ tailWord_2376223).sum := by decide
  have hdescent : baseEnd_2376223 < baseStart_2376223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376244 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2376244 : Nat := 118140960795 + 2376244 * 2 ^ 59
def prefixEnd_2376244 : Nat := 4983230072969 + 3 ^ 40 * 2376244 * 2
def baseEnd_2376244 : Nat := 1220155324362506168121859

theorem tailTrace_2376244 : CollatzResearch.WordTrace tailWord_2376244 prefixEnd_2376244 1220155324362506168121859 := by
  unfold tailWord_2376244
  simp only [CollatzResearch.WordTrace]
  refine ⟨43334369401640646505259893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57779159202187528673679857 43334369401640646505259893)
  ·
    refine ⟨4062597131403810609868115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43334369401640646505259893 4062597131403810609868115)
    ·
      refine ⟨6093895697105715914802173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062597131403810609868115 6093895697105715914802173)
      ·
        refine ⟨2285210886414643468050815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6093895697105715914802173 2285210886414643468050815)
        ·
          refine ⟨3427816329621965202076223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285210886414643468050815 3427816329621965202076223)
          ·
            refine ⟨5141724494432947803114335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427816329621965202076223 5141724494432947803114335)
            ·
              refine ⟨7712586741649421704671503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141724494432947803114335 7712586741649421704671503)
              ·
                refine ⟨11568880112474132557007255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712586741649421704671503 11568880112474132557007255)
                ·
                  refine ⟨17353320168711198835510883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11568880112474132557007255 17353320168711198835510883)
                  ·
                    refine ⟨26029980253066798253266325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17353320168711198835510883 26029980253066798253266325)
                    ·
                      refine ⟨1220155324362506168121859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26029980253066798253266325 1220155324362506168121859)
                      ·
                        rfl

theorem cell23_2376244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2376244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376244 prefixEnd_2376244 := by exact prefixLift 2376244
  have htrace : WordTrace (prefixWord ++ tailWord_2376244) baseStart_2376244 baseEnd_2376244 := by
    simpa [prefixWord, tailWord_2376244, baseEnd_2376244] using wordTrace_append hprefix tailTrace_2376244
  have hstable : (prefixWord ++ tailWord_2376244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376244).length < 2 ^ (prefixWord ++ tailWord_2376244).sum := by decide
  have hdescent : baseEnd_2376244 < baseStart_2376244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376274 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_2376274 : Nat := 118140960795 + 2376274 * 2 ^ 59
def prefixEnd_2376274 : Nat := 4983230072969 + 3 ^ 40 * 2376274 * 2
def baseEnd_2376274 : Nat := 1220170728782141050746721

theorem tailTrace_2376274 : CollatzResearch.WordTrace tailWord_2376274 prefixEnd_2376274 1220170728782141050746721 := by
  unfold tailWord_2376274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21667458248293152033527969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57779888662115072089407917 21667458248293152033527969)
  ·
    refine ⟨16250593686219864025145977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21667458248293152033527969 16250593686219864025145977)
    ·
      refine ⟨12187945264664898018859483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16250593686219864025145977 12187945264664898018859483)
      ·
        refine ⟨18281917896997347028289225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187945264664898018859483 18281917896997347028289225)
        ·
          refine ⟨13711438422748010271216919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281917896997347028289225 13711438422748010271216919)
          ·
            refine ⟨20567157634122015406825379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13711438422748010271216919 20567157634122015406825379)
            ·
              refine ⟨30850736451183023110238069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20567157634122015406825379 30850736451183023110238069)
              ·
                refine ⟨2892256542298408416584819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30850736451183023110238069 2892256542298408416584819)
                ·
                  refine ⟨4338384813447612624877229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892256542298408416584819 4338384813447612624877229)
                  ·
                    refine ⟨1626894305042854734328961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4338384813447612624877229 1626894305042854734328961)
                    ·
                      refine ⟨1220170728782141050746721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626894305042854734328961 1220170728782141050746721)
                      ·
                        rfl

theorem cell23_2376274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_2376274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376274 prefixEnd_2376274 := by exact prefixLift 2376274
  have htrace : WordTrace (prefixWord ++ tailWord_2376274) baseStart_2376274 baseEnd_2376274 := by
    simpa [prefixWord, tailWord_2376274, baseEnd_2376274] using wordTrace_append hprefix tailTrace_2376274
  have hstable : (prefixWord ++ tailWord_2376274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376274).length < 2 ^ (prefixWord ++ tailWord_2376274).sum := by decide
  have hdescent : baseEnd_2376274 < baseStart_2376274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376300 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2376300 : Nat := 118140960795 + 2376300 * 2 ^ 59
def prefixEnd_2376300 : Nat := 4983230072969 + 3 ^ 40 * 2376300 * 2
def baseEnd_2376300 : Nat := 1220184079279157949021601

theorem tailTrace_2376300 : CollatzResearch.WordTrace tailWord_2376300 prefixEnd_2376300 1220184079279157949021601 := by
  unfold tailWord_2376300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43335390645539207287279177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57780520860718943049705569 43335390645539207287279177)
  ·
    refine ⟨32501542984154405465459383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43335390645539207287279177 32501542984154405465459383)
    ·
      refine ⟨48752314476231608198189075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32501542984154405465459383 48752314476231608198189075)
      ·
        refine ⟨73128471714347412297283613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48752314476231608198189075 73128471714347412297283613)
        ·
          refine ⟨27423176892880279611481355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73128471714347412297283613 27423176892880279611481355)
          ·
            refine ⟨41134765339320419417222033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27423176892880279611481355 41134765339320419417222033)
            ·
              refine ⟨30851074004490314562916525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41134765339320419417222033 30851074004490314562916525)
              ·
                refine ⟨11569152751683867961093697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30851074004490314562916525 11569152751683867961093697)
                ·
                  refine ⟨8676864563762900970820273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11569152751683867961093697 8676864563762900970820273)
                  ·
                    refine ⟨6507648422822175728115205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8676864563762900970820273 6507648422822175728115205)
                    ·
                      refine ⟨1220184079279157949021601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6507648422822175728115205 1220184079279157949021601)
                      ·
                        rfl

theorem cell23_2376300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2376300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376300 prefixEnd_2376300 := by exact prefixLift 2376300
  have htrace : WordTrace (prefixWord ++ tailWord_2376300) baseStart_2376300 baseEnd_2376300 := by
    simpa [prefixWord, tailWord_2376300, baseEnd_2376300] using wordTrace_append hprefix tailTrace_2376300
  have hstable : (prefixWord ++ tailWord_2376300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376300).length < 2 ^ (prefixWord ++ tailWord_2376300).sum := by decide
  have hdescent : baseEnd_2376300 < baseStart_2376300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376327 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 5]
def baseStart_2376327 : Nat := 118140960795 + 2376327 * 2 ^ 59
def prefixEnd_2376327 : Nat := 4983230072969 + 3 ^ 40 * 2376327 * 2
def baseEnd_2376327 : Nat := 135577549250758815931553

theorem tailTrace_2376327 : CollatzResearch.WordTrace tailWord_2376327 prefixEnd_2376327 135577549250758815931553 := by
  unfold tailWord_2376327
  simp only [CollatzResearch.WordTrace]
  refine ⟨86671766061980598185791235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57781177374653732123860823 86671766061980598185791235)
  ·
    refine ⟨130007649092970897278686853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86671766061980598185791235 130007649092970897278686853)
    ·
      refine ⟨24376434204932043239753785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130007649092970897278686853 24376434204932043239753785)
      ·
        refine ⟨18282325653699032429815339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24376434204932043239753785 18282325653699032429815339)
        ·
          refine ⟨27423488480548548644723009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18282325653699032429815339 27423488480548548644723009)
          ·
            refine ⟨20567616360411411483542257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27423488480548548644723009 20567616360411411483542257)
            ·
              refine ⟨15425712270308558612656693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20567616360411411483542257 15425712270308558612656693)
              ·
                refine ⟨1446160525341427369936565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15425712270308558612656693 1446160525341427369936565)
                ·
                  refine ⟨135577549250758815931553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1446160525341427369936565 135577549250758815931553)
                  ·
                    rfl

theorem cell23_2376327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 5].length) (baseStart_2376327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376327 prefixEnd_2376327 := by exact prefixLift 2376327
  have htrace : WordTrace (prefixWord ++ tailWord_2376327) baseStart_2376327 baseEnd_2376327 := by
    simpa [prefixWord, tailWord_2376327, baseEnd_2376327] using wordTrace_append hprefix tailTrace_2376327
  have hstable : (prefixWord ++ tailWord_2376327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376327).length < 2 ^ (prefixWord ++ tailWord_2376327).sum := by decide
  have hdescent : baseEnd_2376327 < baseStart_2376327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376338 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_2376338 : Nat := 118140960795 + 2376338 * 2 ^ 59
def prefixEnd_2376338 : Nat := 4983230072969 + 3 ^ 40 * 2376338 * 2
def baseEnd_2376338 : Nat := 1220203591544028800346427

theorem tailTrace_2376338 : CollatzResearch.WordTrace tailWord_2376338 prefixEnd_2376338 1220203591544028800346427 := by
  unfold tailWord_2376338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668041816235186766110417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57781444843293831376294445 21668041816235186766110417)
  ·
    refine ⟨16251031362176390074582813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21668041816235186766110417 16251031362176390074582813)
    ·
      refine ⟨6094136760816146277968555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16251031362176390074582813 6094136760816146277968555)
      ·
        refine ⟨9141205141224219416952833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6094136760816146277968555 9141205141224219416952833)
        ·
          refine ⟨6855903855918164562714625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9141205141224219416952833 6855903855918164562714625)
          ·
            refine ⟨5141927891938623422035969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6855903855918164562714625 5141927891938623422035969)
            ·
              refine ⟨3856445918953967566526977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5141927891938623422035969 3856445918953967566526977)
              ·
                refine ⟨2892334439215475674895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856445918953967566526977 2892334439215475674895233)
                ·
                  refine ⟨2169250829411606756171425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892334439215475674895233 2169250829411606756171425)
                  ·
                    refine ⟨1626938122058705067128569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169250829411606756171425 1626938122058705067128569)
                    ·
                      refine ⟨1220203591544028800346427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626938122058705067128569 1220203591544028800346427)
                      ·
                        rfl

theorem cell23_2376338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_2376338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376338 prefixEnd_2376338 := by exact prefixLift 2376338
  have htrace : WordTrace (prefixWord ++ tailWord_2376338) baseStart_2376338 baseEnd_2376338 := by
    simpa [prefixWord, tailWord_2376338, baseEnd_2376338] using wordTrace_append hprefix tailTrace_2376338
  have hstable : (prefixWord ++ tailWord_2376338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376338).length < 2 ^ (prefixWord ++ tailWord_2376338).sum := by decide
  have hdescent : baseEnd_2376338 < baseStart_2376338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376377 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2376377 : Nat := 118140960795 + 2376377 * 2 ^ 59
def prefixEnd_2376377 : Nat := 4983230072969 + 3 ^ 40 * 2376377 * 2
def baseEnd_2376377 : Nat := 1220223617289554147758747

theorem tailTrace_2376377 : CollatzResearch.WordTrace tailWord_2376377 prefixEnd_2376377 1220223617289554147758747 := by
  unfold tailWord_2376377
  simp only [CollatzResearch.WordTrace]
  refine ⟨86673589711799456725111385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57782393141199637816740923 86673589711799456725111385)
  ·
    refine ⟨65005192283849592543833539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86673589711799456725111385 65005192283849592543833539)
    ·
      refine ⟨97507788425774388815750309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65005192283849592543833539 97507788425774388815750309)
      ·
        refine ⟨18282710329832697902953183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97507788425774388815750309 18282710329832697902953183)
        ·
          refine ⟨27424065494749046854429775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18282710329832697902953183 27424065494749046854429775)
          ·
            refine ⟨41136098242123570281644663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27424065494749046854429775 41136098242123570281644663)
            ·
              refine ⟨61704147363185355422466995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41136098242123570281644663 61704147363185355422466995)
              ·
                refine ⟨92556221044778033133700493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61704147363185355422466995 92556221044778033133700493)
                ·
                  refine ⟨34708582891791762425137685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92556221044778033133700493 34708582891791762425137685)
                  ·
                    refine ⟨1626964823052738863678329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34708582891791762425137685 1626964823052738863678329)
                    ·
                      refine ⟨1220223617289554147758747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626964823052738863678329 1220223617289554147758747)
                      ·
                        rfl

theorem cell23_2376377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2376377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376377 prefixEnd_2376377 := by exact prefixLift 2376377
  have htrace : WordTrace (prefixWord ++ tailWord_2376377) baseStart_2376377 baseEnd_2376377 := by
    simpa [prefixWord, tailWord_2376377, baseEnd_2376377] using wordTrace_append hprefix tailTrace_2376377
  have hstable : (prefixWord ++ tailWord_2376377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376377).length < 2 ^ (prefixWord ++ tailWord_2376377).sum := by decide
  have hdescent : baseEnd_2376377 < baseStart_2376377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376394 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_2376394 : Nat := 118140960795 + 2376394 * 2 ^ 59
def prefixEnd_2376394 : Nat := 4983230072969 + 3 ^ 40 * 2376394 * 2
def baseEnd_2376394 : Nat := 1220232346460680581246169

theorem tailTrace_2376394 : CollatzResearch.WordTrace tailWord_2376394 prefixEnd_2376394 1220232346460680581246169 := by
  unfold tailWord_2376394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668552438184467157120059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57782806501825245752320157 21668552438184467157120059)
  ·
    refine ⟨32502828657276700735680089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21668552438184467157120059 32502828657276700735680089)
    ·
      refine ⟨24377121492957525551760067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32502828657276700735680089 24377121492957525551760067)
      ·
        refine ⟨36565682239436288327640101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24377121492957525551760067 36565682239436288327640101)
        ·
          refine ⟨6856065419894304061432519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36565682239436288327640101 6856065419894304061432519)
          ·
            refine ⟨10284098129841456092148779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856065419894304061432519 10284098129841456092148779)
            ·
              refine ⟨15426147194762184138223169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10284098129841456092148779 15426147194762184138223169)
              ·
                refine ⟨11569610396071638103667377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15426147194762184138223169 11569610396071638103667377)
                ·
                  refine ⟨8677207797053728577750533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11569610396071638103667377 8677207797053728577750533)
                  ·
                    refine ⟨1626976461947574108328225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8677207797053728577750533 1626976461947574108328225)
                    ·
                      refine ⟨1220232346460680581246169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1626976461947574108328225 1220232346460680581246169)
                      ·
                        rfl

theorem cell23_2376394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_2376394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376394 prefixEnd_2376394 := by exact prefixLift 2376394
  have htrace : WordTrace (prefixWord ++ tailWord_2376394) baseStart_2376394 baseEnd_2376394 := by
    simpa [prefixWord, tailWord_2376394, baseEnd_2376394] using wordTrace_append hprefix tailTrace_2376394
  have hstable : (prefixWord ++ tailWord_2376394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376394).length < 2 ^ (prefixWord ++ tailWord_2376394).sum := by decide
  have hdescent : baseEnd_2376394 < baseStart_2376394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376467 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4]
def baseStart_2376467 : Nat := 118140960795 + 2376467 * 2 ^ 59
def prefixEnd_2376467 : Nat := 4983230072969 + 3 ^ 40 * 2376467 * 2
def baseEnd_2376467 : Nat := 1220269830548458795633333

theorem tailTrace_2376467 : CollatzResearch.WordTrace tailWord_2376467 prefixEnd_2376467 1220269830548458795633333 := by
  unfold tailWord_2376467
  simp only [CollatzResearch.WordTrace]
  refine ⟨86676872281473402095887655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57784581520982268063925103 86676872281473402095887655)
  ·
    refine ⟨130015308422210103143831483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86676872281473402095887655 130015308422210103143831483)
    ·
      refine ⟨195022962633315154715747225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130015308422210103143831483 195022962633315154715747225)
      ·
        refine ⟨146267221974986366036810419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195022962633315154715747225 146267221974986366036810419)
        ·
          refine ⟨219400832962479549055215629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146267221974986366036810419 219400832962479549055215629)
          ·
            refine ⟨82275312360929830895705861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219400832962479549055215629 82275312360929830895705861)
            ·
              refine ⟨15426621067674343292944849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82275312360929830895705861 15426621067674343292944849)
              ·
                refine ⟨11569965800755757469708637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15426621067674343292944849 11569965800755757469708637)
                ·
                  refine ⟨4338737175283409051140739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11569965800755757469708637 4338737175283409051140739)
                  ·
                    refine ⟨6508105762925113576711109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4338737175283409051140739 6508105762925113576711109)
                    ·
                      refine ⟨1220269830548458795633333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6508105762925113576711109 1220269830548458795633333)
                      ·
                        rfl

theorem cell23_2376467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_2376467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376467 prefixEnd_2376467 := by exact prefixLift 2376467
  have htrace : WordTrace (prefixWord ++ tailWord_2376467) baseStart_2376467 baseEnd_2376467 := by
    simpa [prefixWord, tailWord_2376467, baseEnd_2376467] using wordTrace_append hprefix tailTrace_2376467
  have hstable : (prefixWord ++ tailWord_2376467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376467).length < 2 ^ (prefixWord ++ tailWord_2376467).sum := by decide
  have hdescent : baseEnd_2376467 < baseStart_2376467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376494 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2376494 : Nat := 118140960795 + 2376494 * 2 ^ 59
def prefixEnd_2376494 : Nat := 4983230072969 + 3 ^ 40 * 2376494 * 2
def baseEnd_2376494 : Nat := 406761231508710063331903

theorem tailTrace_2376494 : CollatzResearch.WordTrace tailWord_2376494 prefixEnd_2376494 406761231508710063331903 := by
  unfold tailWord_2376494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834732131546948213390067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57785238034917057138080357 10834732131546948213390067)
  ·
    refine ⟨16252098197320422320085101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10834732131546948213390067 16252098197320422320085101)
    ·
      refine ⟨6094536823995158370031913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16252098197320422320085101 6094536823995158370031913)
      ·
        refine ⟨4570902617996368777523935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094536823995158370031913 4570902617996368777523935)
        ·
          refine ⟨6856353926994553166285903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570902617996368777523935 6856353926994553166285903)
          ·
            refine ⟨10284530890491829749428855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856353926994553166285903 10284530890491829749428855)
            ·
              refine ⟨15426796335737744624143283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10284530890491829749428855 15426796335737744624143283)
              ·
                refine ⟨23140194503606616936214925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15426796335737744624143283 23140194503606616936214925)
                ·
                  refine ⟨8677572938852481351080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23140194503606616936214925 8677572938852481351080597)
                  ·
                    refine ⟨406761231508710063331903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8677572938852481351080597 406761231508710063331903)
                    ·
                      rfl

theorem cell23_2376494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2376494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376494 prefixEnd_2376494 := by exact prefixLift 2376494
  have htrace : WordTrace (prefixWord ++ tailWord_2376494) baseStart_2376494 baseEnd_2376494 := by
    simpa [prefixWord, tailWord_2376494, baseEnd_2376494] using wordTrace_append hprefix tailTrace_2376494
  have hstable : (prefixWord ++ tailWord_2376494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376494).length < 2 ^ (prefixWord ++ tailWord_2376494).sum := by decide
  have hdescent : baseEnd_2376494 < baseStart_2376494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376511 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 2, 4]
def baseStart_2376511 : Nat := 118140960795 + 2376511 * 2 ^ 59
def prefixEnd_2376511 : Nat := 4983230072969 + 3 ^ 40 * 2376511 * 2
def baseEnd_2376511 : Nat := 406764141232418874494377

theorem tailTrace_2376511 : CollatzResearch.WordTrace tailWord_2376511 prefixEnd_2376511 406764141232418874494377 := by
  unfold tailWord_2376511
  simp only [CollatzResearch.WordTrace]
  refine ⟨86678477093313997610489387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57785651395542665073659591 86678477093313997610489387)
  ·
    refine ⟨130017715639970996415734081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86678477093313997610489387 130017715639970996415734081)
    ·
      refine ⟨97513286729978247311800561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130017715639970996415734081 97513286729978247311800561)
      ·
        refine ⟨73134965047483685483850421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97513286729978247311800561 73134965047483685483850421)
        ·
          refine ⟨6856402973201595514110977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73134965047483685483850421 6856402973201595514110977)
          ·
            refine ⟨5142302229901196635583233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6856402973201595514110977 5142302229901196635583233)
            ·
              refine ⟨3856726672425897476687425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142302229901196635583233 3856726672425897476687425)
              ·
                refine ⟨2892545004319423107515569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856726672425897476687425 2892545004319423107515569)
                ·
                  refine ⟨2169408753239567330636677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892545004319423107515569 2169408753239567330636677)
                  ·
                    refine ⟨406764141232418874494377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169408753239567330636677 406764141232418874494377)
                    ·
                      rfl

theorem cell23_2376511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_2376511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376511 prefixEnd_2376511 := by exact prefixLift 2376511
  have htrace : WordTrace (prefixWord ++ tailWord_2376511) baseStart_2376511 baseEnd_2376511 := by
    simpa [prefixWord, tailWord_2376511, baseEnd_2376511] using wordTrace_append hprefix tailTrace_2376511
  have hstable : (prefixWord ++ tailWord_2376511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376511).length < 2 ^ (prefixWord ++ tailWord_2376511).sum := by decide
  have hdescent : baseEnd_2376511 < baseStart_2376511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376524 : List Nat := [2, 2, 1, 3, 3, 3, 1, 8]
def baseStart_2376524 : Nat := 118140960795 + 2376524 * 2 ^ 59
def prefixEnd_2376524 : Nat := 4983230072969 + 3 ^ 40 * 2376524 * 2
def baseEnd_2376524 : Nat := 45196262923917224911873

theorem tailTrace_2376524 : CollatzResearch.WordTrace tailWord_2376524 prefixEnd_2376524 45196262923917224911873 := by
  unfold tailWord_2376524
  simp only [CollatzResearch.WordTrace]
  refine ⟨43339475621133450415356313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57785967494844600553808417 43339475621133450415356313)
  ·
    refine ⟨32504606715850087811517235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43339475621133450415356313 32504606715850087811517235)
    ·
      refine ⟨48756910073775131717275853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32504606715850087811517235 48756910073775131717275853)
      ·
        refine ⟨18283841277665674393978445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48756910073775131717275853 18283841277665674393978445)
        ·
          refine ⟨6856440479124627897741917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18283841277665674393978445 6856440479124627897741917)
          ·
            refine ⟨2571165179671735461653219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6856440479124627897741917 2571165179671735461653219)
            ·
              refine ⟨3856747769507603192479829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571165179671735461653219 3856747769507603192479829)
              ·
                refine ⟨45196262923917224911873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3856747769507603192479829 45196262923917224911873)
                ·
                  rfl

theorem cell23_2376524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 8].length) (baseStart_2376524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376524 prefixEnd_2376524 := by exact prefixLift 2376524
  have htrace : WordTrace (prefixWord ++ tailWord_2376524) baseStart_2376524 baseEnd_2376524 := by
    simpa [prefixWord, tailWord_2376524, baseEnd_2376524] using wordTrace_append hprefix tailTrace_2376524
  have hstable : (prefixWord ++ tailWord_2376524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376524).length < 2 ^ (prefixWord ++ tailWord_2376524).sum := by decide
  have hdescent : baseEnd_2376524 < baseStart_2376524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376584 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2376584 : Nat := 118140960795 + 2376584 * 2 ^ 59
def prefixEnd_2376584 : Nat := 4983230072969 + 3 ^ 40 * 2376584 * 2
def baseEnd_2376584 : Nat := 406776635928344945956765

theorem tailTrace_2376584 : CollatzResearch.WordTrace tailWord_2376584 prefixEnd_2376584 406776635928344945956765 := by
  unfold tailWord_2376584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43340569811024765538948403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57787426414699687385264537 43340569811024765538948403)
  ·
    refine ⟨65010854716537148308422605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43340569811024765538948403 65010854716537148308422605)
    ·
      refine ⟨24379070518701430615658477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65010854716537148308422605 24379070518701430615658477)
      ·
        refine ⟨9142151444513036480871929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24379070518701430615658477 9142151444513036480871929)
        ·
          refine ⟨6856613583384777360653947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9142151444513036480871929 6856613583384777360653947)
          ·
            refine ⟨10284920375077166040980921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856613583384777360653947 10284920375077166040980921)
            ·
              refine ⟨7713690281307874530735691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10284920375077166040980921 7713690281307874530735691)
              ·
                refine ⟨11570535421961811796103537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7713690281307874530735691 11570535421961811796103537)
                ·
                  refine ⟨8677901566471358847077653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11570535421961811796103537 8677901566471358847077653)
                  ·
                    refine ⟨406776635928344945956765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8677901566471358847077653 406776635928344945956765)
                    ·
                      rfl

theorem cell23_2376584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2376584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376584 prefixEnd_2376584 := by exact prefixLift 2376584
  have htrace : WordTrace (prefixWord ++ tailWord_2376584) baseStart_2376584 baseEnd_2376584 := by
    simpa [prefixWord, tailWord_2376584, baseEnd_2376584] using wordTrace_append hprefix tailTrace_2376584
  have hstable : (prefixWord ++ tailWord_2376584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376584).length < 2 ^ (prefixWord ++ tailWord_2376584).sum := by decide
  have hdescent : baseEnd_2376584 < baseStart_2376584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376598 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2376598 : Nat := 118140960795 + 2376598 * 2 ^ 59
def prefixEnd_2376598 : Nat := 4983230072969 + 3 ^ 40 * 2376598 * 2
def baseEnd_2376598 : Nat := 1220337096514197783095231

theorem tailTrace_2376598 : CollatzResearch.WordTrace tailWord_2376598 prefixEnd_2376598 1220337096514197783095231 := by
  unfold tailWord_2376598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417603140249925716806653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57787766829332540979270965 5417603140249925716806653)
  ·
    refine ⟨2031601177593722143802495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5417603140249925716806653 2031601177593722143802495)
    ·
      refine ⟨3047401766390583215703743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031601177593722143802495 3047401766390583215703743)
      ·
        refine ⟨4571102649585874823555615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047401766390583215703743 4571102649585874823555615)
        ·
          refine ⟨6856653974378812235333423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571102649585874823555615 6856653974378812235333423)
          ·
            refine ⟨10284980961568218353000135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856653974378812235333423 10284980961568218353000135)
            ·
              refine ⟨15427471442352327529500203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10284980961568218353000135 15427471442352327529500203)
              ·
                refine ⟨23141207163528491294250305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15427471442352327529500203 23141207163528491294250305)
                ·
                  refine ⟨17355905372646368470687729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23141207163528491294250305 17355905372646368470687729)
                  ·
                    refine ⟨13016929029484776353015797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17355905372646368470687729 13016929029484776353015797)
                    ·
                      refine ⟨1220337096514197783095231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13016929029484776353015797 1220337096514197783095231)
                      ·
                        rfl

theorem cell23_2376598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2376598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376598 prefixEnd_2376598 := by exact prefixLift 2376598
  have htrace : WordTrace (prefixWord ++ tailWord_2376598) baseStart_2376598 baseEnd_2376598 := by
    simpa [prefixWord, tailWord_2376598, baseEnd_2376598] using wordTrace_append hprefix tailTrace_2376598
  have hstable : (prefixWord ++ tailWord_2376598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376598).length < 2 ^ (prefixWord ++ tailWord_2376598).sum := by decide
  have hdescent : baseEnd_2376598 < baseStart_2376598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376627 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 7]
def baseStart_2376627 : Nat := 118140960795 + 2376627 * 2 ^ 59
def prefixEnd_2376627 : Nat := 4983230072969 + 3 ^ 40 * 2376627 * 2
def baseEnd_2376627 : Nat := 406783995817726056544199

theorem tailTrace_2376627 : CollatzResearch.WordTrace tailWord_2376627 prefixEnd_2376627 406783995817726056544199 := by
  unfold tailWord_2376627
  simp only [CollatzResearch.WordTrace]
  refine ⟨86682707960893749421712135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57788471973929166281141423 86682707960893749421712135)
  ·
    refine ⟨130024061941340624132568203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86682707960893749421712135 130024061941340624132568203)
    ·
      refine ⟨195036092912010936198852305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130024061941340624132568203 195036092912010936198852305)
      ·
        refine ⟨146277069684008202149139229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195036092912010936198852305 146277069684008202149139229)
        ·
          refine ⟨54853901131503075805927211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146277069684008202149139229 54853901131503075805927211)
          ·
            refine ⟨82280851697254613708890817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54853901131503075805927211 82280851697254613708890817)
            ·
              refine ⟨61710638772940960281668113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82280851697254613708890817 61710638772940960281668113)
              ·
                refine ⟨46282979079705720211251085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61710638772940960281668113 46282979079705720211251085)
                ·
                  refine ⟨17356117154889645079219157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46282979079705720211251085 17356117154889645079219157)
                  ·
                    refine ⟨406783995817726056544199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17356117154889645079219157 406783995817726056544199)
                    ·
                      rfl

theorem cell23_2376627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_2376627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376627 prefixEnd_2376627 := by exact prefixLift 2376627
  have htrace : WordTrace (prefixWord ++ tailWord_2376627) baseStart_2376627 baseEnd_2376627 := by
    simpa [prefixWord, tailWord_2376627, baseEnd_2376627] using wordTrace_append hprefix tailTrace_2376627
  have hstable : (prefixWord ++ tailWord_2376627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376627).length < 2 ^ (prefixWord ++ tailWord_2376627).sum := by decide
  have hdescent : baseEnd_2376627 < baseStart_2376627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376684 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2376684 : Nat := 118140960795 + 2376684 * 2 ^ 59
def prefixEnd_2376684 : Nat := 4983230072969 + 3 ^ 40 * 2376684 * 2
def baseEnd_2376684 : Nat := 1220381255850484446619835

theorem tailTrace_2376684 : CollatzResearch.WordTrace tailWord_2376684 prefixEnd_2376684 1220381255850484446619835 := by
  unfold tailWord_2376684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43342393460843624078268553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57789857947791498771024737 43342393460843624078268553)
  ·
    refine ⟨32506795095632718058701415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43342393460843624078268553 32506795095632718058701415)
    ·
      refine ⟨48760192643449077088052123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32506795095632718058701415 48760192643449077088052123)
      ·
        refine ⟨73140288965173615632078185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48760192643449077088052123 73140288965173615632078185)
        ·
          refine ⟨54855216723880211724058639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73140288965173615632078185 54855216723880211724058639)
          ·
            refine ⟨82282825085820317586087959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54855216723880211724058639 82282825085820317586087959)
            ·
              refine ⟨123424237628730476379131939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82282825085820317586087959 123424237628730476379131939)
              ·
                refine ⟨185136356443095714568697909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123424237628730476379131939 185136356443095714568697909)
                ·
                  refine ⟨17356533416540223240815429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185136356443095714568697909 17356533416540223240815429)
                  ·
                    refine ⟨3254350015601291857652893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17356533416540223240815429 3254350015601291857652893)
                    ·
                      refine ⟨1220381255850484446619835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254350015601291857652893 1220381255850484446619835)
                      ·
                        rfl

theorem cell23_2376684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2376684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376684 prefixEnd_2376684 := by exact prefixLift 2376684
  have htrace : WordTrace (prefixWord ++ tailWord_2376684) baseStart_2376684 baseEnd_2376684 := by
    simpa [prefixWord, tailWord_2376684, baseEnd_2376684] using wordTrace_append hprefix tailTrace_2376684
  have hstable : (prefixWord ++ tailWord_2376684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376684).length < 2 ^ (prefixWord ++ tailWord_2376684).sum := by decide
  have hdescent : baseEnd_2376684 < baseStart_2376684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376718 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2376718 : Nat := 118140960795 + 2376718 * 2 ^ 59
def prefixEnd_2376718 : Nat := 4983230072969 + 3 ^ 40 * 2376718 * 2
def baseEnd_2376718 : Nat := 1220398714192737313594679

theorem tailTrace_2376718 : CollatzResearch.WordTrace tailWord_2376718 prefixEnd_2376718 1220398714192737313594679 := by
  unfold tailWord_2376718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10835753375445508995409351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57790684669042714642183205 10835753375445508995409351)
  ·
    refine ⟨16253630063168263493114027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10835753375445508995409351 16253630063168263493114027)
    ·
      refine ⟨24380445094752395239671041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16253630063168263493114027 24380445094752395239671041)
      ·
        refine ⟨18285333821064296429753281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24380445094752395239671041 18285333821064296429753281)
        ·
          refine ⟨13714000365798222322314961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18285333821064296429753281 13714000365798222322314961)
          ·
            refine ⟨10285500274348666741736221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13714000365798222322314961 10285500274348666741736221)
            ·
              refine ⟨3857062602880750028151083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10285500274348666741736221 3857062602880750028151083)
              ·
                refine ⟨5785593904321125042226625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857062602880750028151083 5785593904321125042226625)
                ·
                  refine ⟨4339195428240843781669969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5785593904321125042226625 4339195428240843781669969)
                  ·
                    refine ⟨3254396571180632836252477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339195428240843781669969 3254396571180632836252477)
                    ·
                      refine ⟨1220398714192737313594679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254396571180632836252477 1220398714192737313594679)
                      ·
                        rfl

theorem cell23_2376718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2376718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376718 prefixEnd_2376718 := by exact prefixLift 2376718
  have htrace : WordTrace (prefixWord ++ tailWord_2376718) baseStart_2376718 baseEnd_2376718 := by
    simpa [prefixWord, tailWord_2376718, baseEnd_2376718] using wordTrace_append hprefix tailTrace_2376718
  have hstable : (prefixWord ++ tailWord_2376718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376718).length < 2 ^ (prefixWord ++ tailWord_2376718).sum := by decide
  have hdescent : baseEnd_2376718 < baseStart_2376718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376725 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2376725 : Nat := 118140960795 + 2376725 * 2 ^ 59
def prefixEnd_2376725 : Nat := 4983230072969 + 3 ^ 40 * 2376725 * 2
def baseEnd_2376725 : Nat := 406800769519106262069049

theorem tailTrace_2376725 : CollatzResearch.WordTrace tailWord_2376725 prefixEnd_2376725 406800769519106262069049 := by
  unfold tailWord_2376725
  simp only [CollatzResearch.WordTrace]
  refine ⟨86686282314538712158779629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57790854876359141439186419 86686282314538712158779629)
  ·
    refine ⟨32507355867952017059542361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86686282314538712158779629 32507355867952017059542361)
    ·
      refine ⟨24380516900964012794656771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32507355867952017059542361 24380516900964012794656771)
      ·
        refine ⟨36570775351446019191985157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24380516900964012794656771 36570775351446019191985157)
        ·
          refine ⟨6857020378396128598497217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36570775351446019191985157 6857020378396128598497217)
          ·
            refine ⟨5142765283797096448872913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857020378396128598497217 5142765283797096448872913)
            ·
              refine ⟨3857073962847822336654685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142765283797096448872913 3857073962847822336654685)
              ·
                refine ⟨1446402736067933376245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3857073962847822336654685 1446402736067933376245507)
                ·
                  refine ⟨2169604104101900064368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446402736067933376245507 2169604104101900064368261)
                  ·
                    refine ⟨406800769519106262069049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169604104101900064368261 406800769519106262069049)
                    ·
                      rfl

theorem cell23_2376725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2376725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376725 prefixEnd_2376725 := by exact prefixLift 2376725
  have htrace : WordTrace (prefixWord ++ tailWord_2376725) baseStart_2376725 baseEnd_2376725 := by
    simpa [prefixWord, tailWord_2376725, baseEnd_2376725] using wordTrace_append hprefix tailTrace_2376725
  have hstable : (prefixWord ++ tailWord_2376725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376725).length < 2 ^ (prefixWord ++ tailWord_2376725).sum := by decide
  have hdescent : baseEnd_2376725 < baseStart_2376725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376738 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_2376738 : Nat := 118140960795 + 2376738 * 2 ^ 59
def prefixEnd_2376738 : Nat := 4983230072969 + 3 ^ 40 * 2376738 * 2
def baseEnd_2376738 : Nat := 135600998200647470593843

theorem tailTrace_2376738 : CollatzResearch.WordTrace tailWord_2376738 prefixEnd_2376738 135600998200647470593843 := by
  unfold tailWord_2376738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671689115872903844750717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57791170975661076919335245 21671689115872903844750717)
  ·
    refine ⟨8126883418452338941781519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21671689115872903844750717 8126883418452338941781519)
    ·
      refine ⟨12190325127678508412672279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8126883418452338941781519 12190325127678508412672279)
      ·
        refine ⟨18285487691517762619008419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190325127678508412672279 18285487691517762619008419)
        ·
          refine ⟨27428231537276643928512629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18285487691517762619008419 27428231537276643928512629)
          ·
            refine ⟨2571396706619685368298059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27428231537276643928512629 2571396706619685368298059)
            ·
              refine ⟨3857095059929528052447089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571396706619685368298059 3857095059929528052447089)
              ·
                refine ⟨2892821294947146039335317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857095059929528052447089 2892821294947146039335317)
                ·
                  refine ⟨135600998200647470593843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2892821294947146039335317 135600998200647470593843)
                  ·
                    rfl

theorem cell23_2376738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_2376738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376738 prefixEnd_2376738 := by exact prefixLift 2376738
  have htrace : WordTrace (prefixWord ++ tailWord_2376738) baseStart_2376738 baseEnd_2376738 := by
    simpa [prefixWord, tailWord_2376738, baseEnd_2376738] using wordTrace_append hprefix tailTrace_2376738
  have hstable : (prefixWord ++ tailWord_2376738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376738).length < 2 ^ (prefixWord ++ tailWord_2376738).sum := by decide
  have hdescent : baseEnd_2376738 < baseStart_2376738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376748 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2376748 : Nat := 118140960795 + 2376748 * 2 ^ 59
def prefixEnd_2376748 : Nat := 4983230072969 + 3 ^ 40 * 2376748 * 2
def baseEnd_2376748 : Nat := 1220414118612372196219541

theorem tailTrace_2376748 : CollatzResearch.WordTrace tailWord_2376748 prefixEnd_2376748 1220414118612372196219541 := by
  unfold tailWord_2376748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43343560596727693543433449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57791414128970258057911265 43343560596727693543433449)
  ·
    refine ⟨32507670447545770157575087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43343560596727693543433449 32507670447545770157575087)
    ·
      refine ⟨48761505671318655236362631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32507670447545770157575087 48761505671318655236362631)
      ·
        refine ⟨73142258506977982854543947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48761505671318655236362631 73142258506977982854543947)
        ·
          refine ⟨109713387760466974281815921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73142258506977982854543947 109713387760466974281815921)
          ·
            refine ⟨82285040820350230711361941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109713387760466974281815921 82285040820350230711361941)
            ·
              refine ⟨3857111288453917064595091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82285040820350230711361941 3857111288453917064595091)
              ·
                refine ⟨5785666932680875596892637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857111288453917064595091 5785666932680875596892637)
                ·
                  refine ⟨2169625099755328348834739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785666932680875596892637 2169625099755328348834739)
                  ·
                    refine ⟨3254437649632992523252109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2169625099755328348834739 3254437649632992523252109)
                    ·
                      refine ⟨1220414118612372196219541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254437649632992523252109 1220414118612372196219541)
                      ·
                        rfl

theorem cell23_2376748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2376748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376748 prefixEnd_2376748 := by exact prefixLift 2376748
  have htrace : WordTrace (prefixWord ++ tailWord_2376748) baseStart_2376748 baseEnd_2376748 := by
    simpa [prefixWord, tailWord_2376748, baseEnd_2376748] using wordTrace_append hprefix tailTrace_2376748
  have hstable : (prefixWord ++ tailWord_2376748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376748).length < 2 ^ (prefixWord ++ tailWord_2376748).sum := by decide
  have hdescent : baseEnd_2376748 < baseStart_2376748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376771 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 6, 2]
def baseStart_2376771 : Nat := 118140960795 + 2376771 * 2 ^ 59
def prefixEnd_2376771 : Nat := 4983230072969 + 3 ^ 40 * 2376771 * 2
def baseEnd_2376771 : Nat := 1220425928667425606231935

theorem tailTrace_2376771 : CollatzResearch.WordTrace tailWord_2376771 prefixEnd_2376771 1220425928667425606231935 := by
  unfold tailWord_2376771
  simp only [CollatzResearch.WordTrace]
  refine ⟨86687960072372062014954167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57791973381581374676636111 86687960072372062014954167)
  ·
    refine ⟨130031940108558093022431251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86687960072372062014954167 130031940108558093022431251)
    ·
      refine ⟨195047910162837139533646877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130031940108558093022431251 195047910162837139533646877)
      ·
        refine ⟨73142966311063927325117579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195047910162837139533646877 73142966311063927325117579)
        ·
          refine ⟨109714449466595890987676369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73142966311063927325117579 109714449466595890987676369)
          ·
            refine ⟨82285837099946918240757277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109714449466595890987676369 82285837099946918240757277)
            ·
              refine ⟨30857188912480094340283979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82285837099946918240757277 30857188912480094340283979)
              ·
                refine ⟨46285783368720141510425969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30857188912480094340283979 46285783368720141510425969)
                ·
                  refine ⟨34714337526540106132819477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46285783368720141510425969 34714337526540106132819477)
                  ·
                    refine ⟨1627234571556567474975913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34714337526540106132819477 1627234571556567474975913)
                    ·
                      refine ⟨1220425928667425606231935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627234571556567474975913 1220425928667425606231935)
                      ·
                        rfl

theorem cell23_2376771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_2376771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376771 prefixEnd_2376771 := by exact prefixLift 2376771
  have htrace : WordTrace (prefixWord ++ tailWord_2376771) baseStart_2376771 baseEnd_2376771 := by
    simpa [prefixWord, tailWord_2376771, baseEnd_2376771] using wordTrace_append hprefix tailTrace_2376771
  have hstable : (prefixWord ++ tailWord_2376771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376771).length < 2 ^ (prefixWord ++ tailWord_2376771).sum := by decide
  have hdescent : baseEnd_2376771 < baseStart_2376771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376788 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2376788 : Nat := 118140960795 + 2376788 * 2 ^ 59
def prefixEnd_2376788 : Nat := 4983230072969 + 3 ^ 40 * 2376788 * 2
def baseEnd_2376788 : Nat := 1220434657838552039719357

theorem tailTrace_2376788 : CollatzResearch.WordTrace tailWord_2376788 prefixEnd_2376788 1220434657838552039719357 := by
  unfold tailWord_2376788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43344290056655236959161509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57792386742206982612215345 43344290056655236959161509)
  ·
    refine ⟨8127054385622856929842783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43344290056655236959161509 8127054385622856929842783)
    ·
      refine ⟨12190581578434285394764175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8127054385622856929842783 12190581578434285394764175)
      ·
        refine ⟨18285872367651428092146263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190581578434285394764175 18285872367651428092146263)
        ·
          refine ⟨27428808551477142138219395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18285872367651428092146263 27428808551477142138219395)
          ·
            refine ⟨41143212827215713207329093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27428808551477142138219395 41143212827215713207329093)
            ·
              refine ⟨7714352405102946226374205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41143212827215713207329093 7714352405102946226374205)
              ·
                refine ⟨2892882151913604834890327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7714352405102946226374205 2892882151913604834890327)
                ·
                  refine ⟨4339323227870407252335491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892882151913604834890327 4339323227870407252335491)
                  ·
                    refine ⟨6508984841805610878503237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339323227870407252335491 6508984841805610878503237)
                    ·
                      refine ⟨1220434657838552039719357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6508984841805610878503237 1220434657838552039719357)
                      ·
                        rfl

theorem cell23_2376788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2376788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376788 prefixEnd_2376788 := by exact prefixLift 2376788
  have htrace : WordTrace (prefixWord ++ tailWord_2376788) baseStart_2376788 baseEnd_2376788 := by
    simpa [prefixWord, tailWord_2376788, baseEnd_2376788] using wordTrace_append hprefix tailTrace_2376788
  have hstable : (prefixWord ++ tailWord_2376788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376788).length < 2 ^ (prefixWord ++ tailWord_2376788).sum := by decide
  have hdescent : baseEnd_2376788 < baseStart_2376788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376791 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2376791 : Nat := 118140960795 + 2376791 * 2 ^ 59
def prefixEnd_2376791 : Nat := 4983230072969 + 3 ^ 40 * 2376791 * 2
def baseEnd_2376791 : Nat := 1220436198280515527981843

theorem tailTrace_2376791 : CollatzResearch.WordTrace tailWord_2376791 prefixEnd_2376791 1220436198280515527981843 := by
  unfold tailWord_2376791
  simp only [CollatzResearch.WordTrace]
  refine ⟨86688689532299605430682227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57792459688199736953788151 86688689532299605430682227)
  ·
    refine ⟨130033034298449408146023341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86688689532299605430682227 130033034298449408146023341)
    ·
      refine ⟨48762387861918528054758753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130033034298449408146023341 48762387861918528054758753)
      ·
        refine ⟨36571790896438896041069065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48762387861918528054758753 36571790896438896041069065)
        ·
          refine ⟨27428843172329172030801799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36571790896438896041069065 27428843172329172030801799)
          ·
            refine ⟨41143264758493758046202699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27428843172329172030801799 41143264758493758046202699)
            ·
              refine ⟨61714897137740637069304049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41143264758493758046202699 61714897137740637069304049)
              ·
                refine ⟨46286172853305477801978037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61714897137740637069304049 46286172853305477801978037)
                ·
                  refine ⟨4339328704997388543935441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46286172853305477801978037 4339328704997388543935441)
                  ·
                    refine ⟨3254496528748041407951581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4339328704997388543935441 3254496528748041407951581)
                    ·
                      refine ⟨1220436198280515527981843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254496528748041407951581 1220436198280515527981843)
                      ·
                        rfl

theorem cell23_2376791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2376791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376791 prefixEnd_2376791 := by exact prefixLift 2376791
  have htrace : WordTrace (prefixWord ++ tailWord_2376791) baseStart_2376791 baseEnd_2376791 := by
    simpa [prefixWord, tailWord_2376791, baseEnd_2376791] using wordTrace_append hprefix tailTrace_2376791
  have hstable : (prefixWord ++ tailWord_2376791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376791).length < 2 ^ (prefixWord ++ tailWord_2376791).sum := by decide
  have hdescent : baseEnd_2376791 < baseStart_2376791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376855 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2376855 : Nat := 118140960795 + 2376855 * 2 ^ 59
def prefixEnd_2376855 : Nat := 4983230072969 + 3 ^ 40 * 2376855 * 2
def baseEnd_2376855 : Nat := 1220469061042403277581549

theorem tailTrace_2376855 : CollatzResearch.WordTrace tailWord_2376855 prefixEnd_2376855 1220469061042403277581549 := by
  unfold tailWord_2376855
  simp only [CollatzResearch.WordTrace]
  refine ⟨86691023804067744361012019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57794015869378496240674679 86691023804067744361012019)
  ·
    refine ⟨130036535706101616541518029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86691023804067744361012019 130036535706101616541518029)
    ·
      refine ⟨48763700889788106203069261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130036535706101616541518029 48763700889788106203069261)
      ·
        refine ⟨18286387833670539826150973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48763700889788106203069261 18286387833670539826150973)
        ·
          refine ⟨6857395437626452434806615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18286387833670539826150973 6857395437626452434806615)
          ·
            refine ⟨10286093156439678652209923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857395437626452434806615 10286093156439678652209923)
            ·
              refine ⟨15429139734659517978314885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286093156439678652209923 15429139734659517978314885)
              ·
                refine ⟨2892963700248659620934041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15429139734659517978314885 2892963700248659620934041)
                ·
                  refine ⟨2169722775186494715700531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892963700248659620934041 2169722775186494715700531)
                  ·
                    refine ⟨3254584162779742073550797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2169722775186494715700531 3254584162779742073550797)
                    ·
                      refine ⟨1220469061042403277581549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254584162779742073550797 1220469061042403277581549)
                      ·
                        rfl

theorem cell23_2376855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2376855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376855 prefixEnd_2376855 := by exact prefixLift 2376855
  have htrace : WordTrace (prefixWord ++ tailWord_2376855) baseStart_2376855 baseEnd_2376855 := by
    simpa [prefixWord, tailWord_2376855, baseEnd_2376855] using wordTrace_append hprefix tailTrace_2376855
  have hstable : (prefixWord ++ tailWord_2376855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376855).length < 2 ^ (prefixWord ++ tailWord_2376855).sum := by decide
  have hdescent : baseEnd_2376855 < baseStart_2376855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376856 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2376856 : Nat := 118140960795 + 2376856 * 2 ^ 59
def prefixEnd_2376856 : Nat := 4983230072969 + 3 ^ 40 * 2376856 * 2
def baseEnd_2376856 : Nat := 1220469574523057773669045

theorem tailTrace_2376856 : CollatzResearch.WordTrace tailWord_2376856 prefixEnd_2376856 1220469574523057773669045 := by
  unfold tailWord_2376856
  simp only [CollatzResearch.WordTrace]
  refine ⟨43345530138532060765899211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57794040184709414354532281 43345530138532060765899211)
  ·
    refine ⟨65018295207798091148848817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43345530138532060765899211 65018295207798091148848817)
    ·
      refine ⟨48763721405848568361636613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65018295207798091148848817 48763721405848568361636613)
      ·
        refine ⟨9143197763596606567806865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48763721405848568361636613 9143197763596606567806865)
        ·
          refine ⟨6857398322697454925855149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9143197763596606567806865 6857398322697454925855149)
          ·
            refine ⟨2571524371011545597195681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6857398322697454925855149 2571524371011545597195681)
            ·
              refine ⟨1928643278258659197896761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571524371011545597195681 1928643278258659197896761)
              ·
                refine ⟨1446482458693994398422571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928643278258659197896761 1446482458693994398422571)
                ·
                  refine ⟨2169723688040991597633857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446482458693994398422571 2169723688040991597633857)
                  ·
                    refine ⟨1627292766030743698225393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169723688040991597633857 1627292766030743698225393)
                    ·
                      refine ⟨1220469574523057773669045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627292766030743698225393 1220469574523057773669045)
                      ·
                        rfl

theorem cell23_2376856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2376856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376856 prefixEnd_2376856 := by exact prefixLift 2376856
  have htrace : WordTrace (prefixWord ++ tailWord_2376856) baseStart_2376856 baseEnd_2376856 := by
    simpa [prefixWord, tailWord_2376856, baseEnd_2376856] using wordTrace_append hprefix tailTrace_2376856
  have hstable : (prefixWord ++ tailWord_2376856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376856).length < 2 ^ (prefixWord ++ tailWord_2376856).sum := by decide
  have hdescent : baseEnd_2376856 < baseStart_2376856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376861 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2376861 : Nat := 118140960795 + 2376861 * 2 ^ 59
def prefixEnd_2376861 : Nat := 4983230072969 + 3 ^ 40 * 2376861 * 2
def baseEnd_2376861 : Nat := 1220472141926330254106521

theorem tailTrace_2376861 : CollatzResearch.WordTrace tailWord_2376861 prefixEnd_2376861 1220472141926330254106521 := by
  unfold tailWord_2376861
  simp only [CollatzResearch.WordTrace]
  refine ⟨86691242642046007385730437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57794161761364004923820291 86691242642046007385730437)
  ·
    refine ⟨16254607995383626384824457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86691242642046007385730437 16254607995383626384824457)
    ·
      refine ⟨12190955996537719788618343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16254607995383626384824457 12190955996537719788618343)
      ·
        refine ⟨18286433994806579682927515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190955996537719788618343 18286433994806579682927515)
        ·
          refine ⟨27429650992209869524391273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18286433994806579682927515 27429650992209869524391273)
          ·
            refine ⟨20572238244157402143293455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27429650992209869524391273 20572238244157402143293455)
            ·
              refine ⟨30858357366236103214940183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20572238244157402143293455 30858357366236103214940183)
              ·
                refine ⟨46287536049354154822410275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30858357366236103214940183 46287536049354154822410275)
                ·
                  refine ⟨69431304074031232233615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46287536049354154822410275 69431304074031232233615413)
                  ·
                    refine ⟨6509184756940428021901445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69431304074031232233615413 6509184756940428021901445)
                    ·
                      refine ⟨1220472141926330254106521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6509184756940428021901445 1220472141926330254106521)
                      ·
                        rfl

theorem cell23_2376861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2376861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376861 prefixEnd_2376861 := by exact prefixLift 2376861
  have htrace : WordTrace (prefixWord ++ tailWord_2376861) baseStart_2376861 baseEnd_2376861 := by
    simpa [prefixWord, tailWord_2376861, baseEnd_2376861] using wordTrace_append hprefix tailTrace_2376861
  have hstable : (prefixWord ++ tailWord_2376861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376861).length < 2 ^ (prefixWord ++ tailWord_2376861).sum := by decide
  have hdescent : baseEnd_2376861 < baseStart_2376861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376928 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2376928 : Nat := 118140960795 + 2376928 * 2 ^ 59
def prefixEnd_2376928 : Nat := 4983230072969 + 3 ^ 40 * 2376928 * 2
def baseEnd_2376928 : Nat := 1220506545130181491968713

theorem tailTrace_2376928 : CollatzResearch.WordTrace tailWord_2376928 prefixEnd_2376928 1220506545130181491968713 := by
  unfold tailWord_2376928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43346843166401638914209719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57795790888535518552279625 43346843166401638914209719)
  ·
    refine ⟨65020264749602458371314579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43346843166401638914209719 65020264749602458371314579)
    ·
      refine ⟨97530397124403687556971869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65020264749602458371314579 97530397124403687556971869)
      ·
        refine ⟨36573898921651382833864451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97530397124403687556971869 36573898921651382833864451)
        ·
          refine ⟨54860848382477074250796677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36573898921651382833864451 54860848382477074250796677)
          ·
            refine ⟨10286409071714451422024377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54860848382477074250796677 10286409071714451422024377)
            ·
              refine ⟨7714806803785838566518283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10286409071714451422024377 7714806803785838566518283)
              ·
                refine ⟨11572210205678757849777425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7714806803785838566518283 11572210205678757849777425)
                ·
                  refine ⟨8679157654259068387333069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11572210205678757849777425 8679157654259068387333069)
                  ·
                    refine ⟨3254684120347150645249901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8679157654259068387333069 3254684120347150645249901)
                    ·
                      refine ⟨1220506545130181491968713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254684120347150645249901 1220506545130181491968713)
                      ·
                        rfl

theorem cell23_2376928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2376928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376928 prefixEnd_2376928 := by exact prefixLift 2376928
  have htrace : WordTrace (prefixWord ++ tailWord_2376928) baseStart_2376928 baseEnd_2376928 := by
    simpa [prefixWord, tailWord_2376928, baseEnd_2376928] using wordTrace_append hprefix tailTrace_2376928
  have hstable : (prefixWord ++ tailWord_2376928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376928).length < 2 ^ (prefixWord ++ tailWord_2376928).sum := by decide
  have hdescent : baseEnd_2376928 < baseStart_2376928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376929 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_2376929 : Nat := 118140960795 + 2376929 * 2 ^ 59
def prefixEnd_2376929 : Nat := 4983230072969 + 3 ^ 40 * 2376929 * 2
def baseEnd_2376929 : Nat := 1220507058610835988056209

theorem tailTrace_2376929 : CollatzResearch.WordTrace tailWord_2376929 prefixEnd_2376929 1220507058610835988056209 := by
  unfold tailWord_2376929
  simp only [CollatzResearch.WordTrace]
  refine ⟨86693722805799654999205841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57795815203866436666137227 86693722805799654999205841)
  ·
    refine ⟨65020292104349741249404381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86693722805799654999205841 65020292104349741249404381)
    ·
      refine ⟨24382609539131152968526643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65020292104349741249404381 24382609539131152968526643)
      ·
        refine ⟨36573914308696729452789965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24382609539131152968526643 36573914308696729452789965)
        ·
          refine ⟨13715217865761273544796237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36573914308696729452789965 13715217865761273544796237)
          ·
            refine ⟨5143206699660477579298589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13715217865761273544796237 5143206699660477579298589)
            ·
              refine ⟨1928702512372679092236971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5143206699660477579298589 1928702512372679092236971)
              ·
                refine ⟨2893053768559018638355457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928702512372679092236971 2893053768559018638355457)
                ·
                  refine ⟨2169790326419263978766593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893053768559018638355457 2169790326419263978766593)
                  ·
                    refine ⟨1627342744814447984074945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169790326419263978766593 1627342744814447984074945)
                    ·
                      refine ⟨1220507058610835988056209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627342744814447984074945 1220507058610835988056209)
                      ·
                        rfl

theorem cell23_2376929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_2376929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376929 prefixEnd_2376929 := by exact prefixLift 2376929
  have htrace : WordTrace (prefixWord ++ tailWord_2376929) baseStart_2376929 baseEnd_2376929 := by
    simpa [prefixWord, tailWord_2376929, baseEnd_2376929] using wordTrace_append hprefix tailTrace_2376929
  have hstable : (prefixWord ++ tailWord_2376929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376929).length < 2 ^ (prefixWord ++ tailWord_2376929).sum := by decide
  have hdescent : baseEnd_2376929 < baseStart_2376929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376988 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2376988 : Nat := 118140960795 + 2376988 * 2 ^ 59
def prefixEnd_2376988 : Nat := 4983230072969 + 3 ^ 40 * 2376988 * 2
def baseEnd_2376988 : Nat := 1220537353969451257218437

theorem tailTrace_2376988 : CollatzResearch.WordTrace tailWord_2376988 prefixEnd_2376988 1220537353969451257218437 := by
  unfold tailWord_2376988
  simp only [CollatzResearch.WordTrace]
  refine ⟨43347937356292954037801809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57797249808390605383735745 43347937356292954037801809)
  ·
    refine ⟨32510953017219715528351357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43347937356292954037801809 32510953017219715528351357)
    ·
      refine ⟨12191607381457393323131759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32510953017219715528351357 12191607381457393323131759)
      ·
        refine ⟨18287411072186089984697639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12191607381457393323131759 18287411072186089984697639)
        ·
          refine ⟨27431116608279134977046459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18287411072186089984697639 27431116608279134977046459)
          ·
            refine ⟨41146674912418702465569689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27431116608279134977046459 41146674912418702465569689)
            ·
              refine ⟨30860006184314026849177267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41146674912418702465569689 30860006184314026849177267)
              ·
                refine ⟨46290009276471040273765901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30860006184314026849177267 46290009276471040273765901)
                ·
                  refine ⟨17358753478676640102662213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46290009276471040273765901 17358753478676640102662213)
                  ·
                    refine ⟨3254766277251870019249165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17358753478676640102662213 3254766277251870019249165)
                    ·
                      refine ⟨1220537353969451257218437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254766277251870019249165 1220537353969451257218437)
                      ·
                        rfl

theorem cell23_2376988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2376988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2376988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2376988 prefixEnd_2376988 := by exact prefixLift 2376988
  have htrace : WordTrace (prefixWord ++ tailWord_2376988) baseStart_2376988 baseEnd_2376988 := by
    simpa [prefixWord, tailWord_2376988, baseEnd_2376988] using wordTrace_append hprefix tailTrace_2376988
  have hstable : (prefixWord ++ tailWord_2376988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376988).length < 2 ^ (prefixWord ++ tailWord_2376988).sum := by decide
  have hdescent : baseEnd_2376988 < baseStart_2376988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377002 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2377002 : Nat := 118140960795 + 2377002 * 2 ^ 59
def prefixEnd_2377002 : Nat := 4983230072969 + 3 ^ 40 * 2377002 * 2
def baseEnd_2377002 : Nat := 1220544542698614202443373

theorem tailTrace_2377002 : CollatzResearch.WordTrace tailWord_2377002 prefixEnd_2377002 1220544542698614202443373 := by
  unfold tailWord_2377002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674096333633797116653315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57797590223023458977742173 21674096333633797116653315)
  ·
    refine ⟨32511144500450695674979973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21674096333633797116653315 32511144500450695674979973)
    ·
      refine ⟨6095839593834505439058745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32511144500450695674979973 6095839593834505439058745)
      ·
        refine ⟨4571879695375879079294059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095839593834505439058745 4571879695375879079294059)
        ·
          refine ⟨6857819543063818618941089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571879695375879079294059 6857819543063818618941089)
          ·
            refine ⟨5143364657297863964205817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857819543063818618941089 5143364657297863964205817)
            ·
              refine ⟨3857523492973397973154363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5143364657297863964205817 3857523492973397973154363)
              ·
                refine ⟨5786285239460096959731545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857523492973397973154363 5786285239460096959731545)
                ·
                  refine ⟨4339713929595072719798659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5786285239460096959731545 4339713929595072719798659)
                  ·
                    refine ⟨6509570894392609079697989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339713929595072719798659 6509570894392609079697989)
                    ·
                      refine ⟨1220544542698614202443373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6509570894392609079697989 1220544542698614202443373)
                      ·
                        rfl

theorem cell23_2377002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2377002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377002 prefixEnd_2377002 := by exact prefixLift 2377002
  have htrace : WordTrace (prefixWord ++ tailWord_2377002) baseStart_2377002 baseEnd_2377002 := by
    simpa [prefixWord, tailWord_2377002, baseEnd_2377002] using wordTrace_append hprefix tailTrace_2377002
  have hstable : (prefixWord ++ tailWord_2377002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377002).length < 2 ^ (prefixWord ++ tailWord_2377002).sum := by decide
  have hdescent : baseEnd_2377002 < baseStart_2377002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377025 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 6]
def baseStart_2377025 : Nat := 118140960795 + 2377025 * 2 ^ 59
def prefixEnd_2377025 : Nat := 4983230072969 + 3 ^ 40 * 2377025 * 2
def baseEnd_2377025 : Nat := 135617372528185290272863

theorem tailTrace_2377025 : CollatzResearch.WordTrace tailWord_2377025 prefixEnd_2377025 135617372528185290272863 := by
  unfold tailWord_2377025
  simp only [CollatzResearch.WordTrace]
  refine ⟨86697224213451863394700529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57798149475634575596467019 86697224213451863394700529)
  ·
    refine ⟨65022918160088897546025397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86697224213451863394700529 65022918160088897546025397)
    ·
      refine ⟨6095898577508334144939881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65022918160088897546025397 6095898577508334144939881)
      ·
        refine ⟨4571923933131250608704911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095898577508334144939881 4571923933131250608704911)
        ·
          refine ⟨6857885899696875913057367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571923933131250608704911 6857885899696875913057367)
          ·
            refine ⟨10286828849545313869586051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857885899696875913057367 10286828849545313869586051)
            ·
              refine ⟨15430243274317970804379077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286828849545313869586051 15430243274317970804379077)
              ·
                refine ⟨2893170613934619525821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15430243274317970804379077 2893170613934619525821077)
                ·
                  refine ⟨135617372528185290272863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2893170613934619525821077 135617372528185290272863)
                  ·
                    rfl

theorem cell23_2377025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_2377025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377025 prefixEnd_2377025 := by exact prefixLift 2377025
  have htrace : WordTrace (prefixWord ++ tailWord_2377025) baseStart_2377025 baseEnd_2377025 := by
    simpa [prefixWord, tailWord_2377025, baseEnd_2377025] using wordTrace_append hprefix tailTrace_2377025
  have hstable : (prefixWord ++ tailWord_2377025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377025).length < 2 ^ (prefixWord ++ tailWord_2377025).sum := by decide
  have hdescent : baseEnd_2377025 < baseStart_2377025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377038 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2377038 : Nat := 118140960795 + 2377038 * 2 ^ 59
def prefixEnd_2377038 : Nat := 4983230072969 + 3 ^ 40 * 2377038 * 2
def baseEnd_2377038 : Nat := 406854342667392020531069

theorem tailTrace_2377038 : CollatzResearch.WordTrace tailWord_2377038 prefixEnd_2377038 406854342667392020531069 := by
  unfold tailWord_2377038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837212295300595826865471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57798465574936511076615845 10837212295300595826865471)
  ·
    refine ⟨16255818442950893740298207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10837212295300595826865471 16255818442950893740298207)
    ·
      refine ⟨24383727664426340610447311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16255818442950893740298207 24383727664426340610447311)
      ·
        refine ⟨36575591496639510915670967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24383727664426340610447311 36575591496639510915670967)
        ·
          refine ⟨54863387244959266373506451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36575591496639510915670967 54863387244959266373506451)
          ·
            refine ⟨82295080867438899560259677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54863387244959266373506451 82295080867438899560259677)
            ·
              refine ⟨30860655325289587335097379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82295080867438899560259677 30860655325289587335097379)
              ·
                refine ⟨46290982987934381002646069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30860655325289587335097379 46290982987934381002646069)
                ·
                  refine ⟨4339779655118848218998069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46290982987934381002646069 4339779655118848218998069)
                  ·
                    refine ⟨406854342667392020531069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4339779655118848218998069 406854342667392020531069)
                    ·
                      rfl

theorem cell23_2377038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2377038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377038 prefixEnd_2377038 := by exact prefixLift 2377038
  have htrace : WordTrace (prefixWord ++ tailWord_2377038) baseStart_2377038 baseEnd_2377038 := by
    simpa [prefixWord, tailWord_2377038, baseEnd_2377038] using wordTrace_append hprefix tailTrace_2377038
  have hstable : (prefixWord ++ tailWord_2377038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377038).length < 2 ^ (prefixWord ++ tailWord_2377038).sum := by decide
  have hdescent : baseEnd_2377038 < baseStart_2377038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377053 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2377053 : Nat := 118140960795 + 2377053 * 2 ^ 59
def prefixEnd_2377053 : Nat := 4983230072969 + 3 ^ 40 * 2377053 * 2
def baseEnd_2377053 : Nat := 1220570730211993502905639

theorem tailTrace_2377053 : CollatzResearch.WordTrace tailWord_2377053 prefixEnd_2377053 1220570730211993502905639 := by
  unfold tailWord_2377053
  simp only [CollatzResearch.WordTrace]
  refine ⟨86698245457350424176719813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57798830304900282784479875 86698245457350424176719813)
  ·
    refine ⟨16255921023253204533134965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86698245457350424176719813 16255921023253204533134965)
    ·
      refine ⟨1523992595929987924981403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16255921023253204533134965 1523992595929987924981403)
      ·
        refine ⟨2285988893894981887472105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523992595929987924981403 2285988893894981887472105)
        ·
          refine ⟨1714491670421236415604079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2285988893894981887472105 1714491670421236415604079)
          ·
            refine ⟨2571737505631854623406119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714491670421236415604079 2571737505631854623406119)
            ·
              refine ⟨3857606258447781935109179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571737505631854623406119 3857606258447781935109179)
              ·
                refine ⟨5786409387671672902663769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857606258447781935109179 5786409387671672902663769)
                ·
                  refine ⟨4339807040753754676997827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5786409387671672902663769 4339807040753754676997827)
                  ·
                    refine ⟨6509710561130632015496741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4339807040753754676997827 6509710561130632015496741)
                    ·
                      refine ⟨1220570730211993502905639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6509710561130632015496741 1220570730211993502905639)
                      ·
                        rfl

theorem cell23_2377053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2377053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377053 prefixEnd_2377053 := by exact prefixLift 2377053
  have htrace : WordTrace (prefixWord ++ tailWord_2377053) baseStart_2377053 baseEnd_2377053 := by
    simpa [prefixWord, tailWord_2377053, baseEnd_2377053] using wordTrace_append hprefix tailTrace_2377053
  have hstable : (prefixWord ++ tailWord_2377053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377053).length < 2 ^ (prefixWord ++ tailWord_2377053).sum := by decide
  have hdescent : baseEnd_2377053 < baseStart_2377053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377069 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2377069 : Nat := 118140960795 + 2377069 * 2 ^ 59
def prefixEnd_2377069 : Nat := 4983230072969 + 3 ^ 40 * 2377069 * 2
def baseEnd_2377069 : Nat := 1220578945902465440305565

theorem tailTrace_2377069 : CollatzResearch.WordTrace tailWord_2377069 prefixEnd_2377069 1220578945902465440305565 := by
  unfold tailWord_2377069
  simp only [CollatzResearch.WordTrace]
  refine ⟨86698829025292458909302261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57799219350194972606201507 86698829025292458909302261)
  ·
    refine ⟨8128015221121168022747087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86698829025292458909302261 8128015221121168022747087)
    ·
      refine ⟨12192022831681752034120631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128015221121168022747087 12192022831681752034120631)
      ·
        refine ⟨18288034247522628051180947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192022831681752034120631 18288034247522628051180947)
        ·
          refine ⟨27432051371283942076771421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18288034247522628051180947 27432051371283942076771421)
          ·
            refine ⟨10287019264231478278789283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27432051371283942076771421 10287019264231478278789283)
            ·
              refine ⟨15430528896347217418183925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10287019264231478278789283 15430528896347217418183925)
              ·
                refine ⟨1446612084032551632954743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15430528896347217418183925 1446612084032551632954743)
                ·
                  refine ⟨2169918126048827449432115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446612084032551632954743 2169918126048827449432115)
                  ·
                    refine ⟨3254877189073241174148173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2169918126048827449432115 3254877189073241174148173)
                    ·
                      refine ⟨1220578945902465440305565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3254877189073241174148173 1220578945902465440305565)
                      ·
                        rfl

theorem cell23_2377069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2377069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377069 prefixEnd_2377069 := by exact prefixLift 2377069
  have htrace : WordTrace (prefixWord ++ tailWord_2377069) baseStart_2377069 baseEnd_2377069 := by
    simpa [prefixWord, tailWord_2377069, baseEnd_2377069] using wordTrace_append hprefix tailTrace_2377069
  have hstable : (prefixWord ++ tailWord_2377069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377069).length < 2 ^ (prefixWord ++ tailWord_2377069).sum := by decide
  have hdescent : baseEnd_2377069 < baseStart_2377069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377085 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2377085 : Nat := 118140960795 + 2377085 * 2 ^ 59
def prefixEnd_2377085 : Nat := 4983230072969 + 3 ^ 40 * 2377085 * 2
def baseEnd_2377085 : Nat := 406862387197645792568497

theorem tailTrace_2377085 : CollatzResearch.WordTrace tailWord_2377085 prefixEnd_2377085 406862387197645792568497 := by
  unfold tailWord_2377085
  simp only [CollatzResearch.WordTrace]
  refine ⟨86699412593234493641884709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57799608395489662427923139 86699412593234493641884709)
  ·
    refine ⟨16256139861231467557853383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86699412593234493641884709 16256139861231467557853383)
    ·
      refine ⟨24384209791847201336780075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16256139861231467557853383 24384209791847201336780075)
      ·
        refine ⟨36576314687770802005170113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24384209791847201336780075 36576314687770802005170113)
        ·
          refine ⟨27432236015828101503877585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36576314687770802005170113 27432236015828101503877585)
          ·
            refine ⟨20574177011871076127908189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27432236015828101503877585 20574177011871076127908189)
            ·
              refine ⟨7715316379451653547965571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20574177011871076127908189 7715316379451653547965571)
              ·
                refine ⟨11572974569177480321948357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715316379451653547965571 11572974569177480321948357)
                ·
                  refine ⟨2169932731720777560365317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11572974569177480321948357 2169932731720777560365317)
                  ·
                    refine ⟨406862387197645792568497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2169932731720777560365317 406862387197645792568497)
                    ·
                      rfl

theorem cell23_2377085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2377085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377085 prefixEnd_2377085 := by exact prefixLift 2377085
  have htrace : WordTrace (prefixWord ++ tailWord_2377085) baseStart_2377085 baseEnd_2377085 := by
    simpa [prefixWord, tailWord_2377085, baseEnd_2377085] using wordTrace_append hprefix tailTrace_2377085
  have hstable : (prefixWord ++ tailWord_2377085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377085).length < 2 ^ (prefixWord ++ tailWord_2377085).sum := by decide
  have hdescent : baseEnd_2377085 < baseStart_2377085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377088 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2377088 : Nat := 118140960795 + 2377088 * 2 ^ 59
def prefixEnd_2377088 : Nat := 4983230072969 + 3 ^ 40 * 2377088 * 2
def baseEnd_2377088 : Nat := 1220588702034900865967977

theorem tailTrace_2377088 : CollatzResearch.WordTrace tailWord_2377088 prefixEnd_2377088 1220588702034900865967977 := by
  unfold tailWord_2377088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43349761006111812577121959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57799681341482416769495945 43349761006111812577121959)
  ·
    refine ⟨65024641509167718865682939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43349761006111812577121959 65024641509167718865682939)
    ·
      refine ⟨97536962263751578298524409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65024641509167718865682939 97536962263751578298524409)
      ·
        refine ⟨73152721697813683723893307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97536962263751578298524409 73152721697813683723893307)
        ·
          refine ⟨109729082546720525585839961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73152721697813683723893307 109729082546720525585839961)
          ·
            refine ⟨82296811910040394189379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109729082546720525585839961 82296811910040394189379971)
            ·
              refine ⟨123445217865060591284069957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82296811910040394189379971 123445217865060591284069957)
              ·
                refine ⟨23145978349698860865763117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123445217865060591284069957 23145978349698860865763117)
                ·
                  refine ⟨8679741881137072824661169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23145978349698860865763117 8679741881137072824661169)
                  ·
                    refine ⟨6509806410852804618495877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8679741881137072824661169 6509806410852804618495877)
                    ·
                      refine ⟨1220588702034900865967977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6509806410852804618495877 1220588702034900865967977)
                      ·
                        rfl

theorem cell23_2377088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2377088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377088 prefixEnd_2377088 := by exact prefixLift 2377088
  have htrace : WordTrace (prefixWord ++ tailWord_2377088) baseStart_2377088 baseEnd_2377088 := by
    simpa [prefixWord, tailWord_2377088, baseEnd_2377088] using wordTrace_append hprefix tailTrace_2377088
  have hstable : (prefixWord ++ tailWord_2377088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377088).length < 2 ^ (prefixWord ++ tailWord_2377088).sum := by decide
  have hdescent : baseEnd_2377088 < baseStart_2377088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377095 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2377095 : Nat := 118140960795 + 2377095 * 2 ^ 59
def prefixEnd_2377095 : Nat := 4983230072969 + 3 ^ 40 * 2377095 * 2
def baseEnd_2377095 : Nat := 1220592296399482338580445

theorem tailTrace_2377095 : CollatzResearch.WordTrace tailWord_2377095 prefixEnd_2377095 1220592296399482338580445 := by
  unfold tailWord_2377095
  simp only [CollatzResearch.WordTrace]
  refine ⟨86699777323198265349748739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57799851548798843566499159 86699777323198265349748739)
  ·
    refine ⟨130049665984797398024623109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86699777323198265349748739 130049665984797398024623109)
    ·
      refine ⟨24384312372149512129616833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130049665984797398024623109 24384312372149512129616833)
      ·
        refine ⟨18288234279112134097212625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24384312372149512129616833 18288234279112134097212625)
        ·
          refine ⟨13716175709334100572909469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18288234279112134097212625 13716175709334100572909469)
          ·
            refine ⟨5143565891000287714841051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13716175709334100572909469 5143565891000287714841051)
            ·
              refine ⟨7715348836500431572261577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143565891000287714841051 7715348836500431572261577)
              ·
                refine ⟨5786511627375323679196183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7715348836500431572261577 5786511627375323679196183)
                ·
                  refine ⟨8679767441062985518794275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786511627375323679196183 8679767441062985518794275)
                  ·
                    refine ⟨13019651161594478278191413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8679767441062985518794275 13019651161594478278191413)
                    ·
                      refine ⟨1220592296399482338580445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13019651161594478278191413 1220592296399482338580445)
                      ·
                        rfl

theorem cell23_2377095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2377095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377095 prefixEnd_2377095 := by exact prefixLift 2377095
  have htrace : WordTrace (prefixWord ++ tailWord_2377095) baseStart_2377095 baseEnd_2377095 := by
    simpa [prefixWord, tailWord_2377095, baseEnd_2377095] using wordTrace_append hprefix tailTrace_2377095
  have hstable : (prefixWord ++ tailWord_2377095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377095).length < 2 ^ (prefixWord ++ tailWord_2377095).sum := by decide
  have hdescent : baseEnd_2377095 < baseStart_2377095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377168 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2377168 : Nat := 118140960795 + 2377168 * 2 ^ 59
def prefixEnd_2377168 : Nat := 4983230072969 + 3 ^ 40 * 2377168 * 2
def baseEnd_2377168 : Nat := 1220629780487260552967609

theorem tailTrace_2377168 : CollatzResearch.WordTrace tailWord_2377168 prefixEnd_2377168 1220629780487260552967609 := by
  unfold tailWord_2377168
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351219925966899408578079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57801626567955865878104105 43351219925966899408578079)
  ·
    refine ⟨65026829888950349112867119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43351219925966899408578079 65026829888950349112867119)
    ·
      refine ⟨97540244833425523669300679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65026829888950349112867119 97540244833425523669300679)
      ·
        refine ⟨146310367250138285503951019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97540244833425523669300679 146310367250138285503951019)
        ·
          refine ⟨219465550875207428255926529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146310367250138285503951019 219465550875207428255926529)
          ·
            refine ⟨164599163156405571191944897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219465550875207428255926529 164599163156405571191944897)
            ·
              refine ⟨123449372367304178393958673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164599163156405571191944897 123449372367304178393958673)
              ·
                refine ⟨92587029275478133795469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123449372367304178393958673 92587029275478133795469005)
                ·
                  refine ⟨34720135978304300173300877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92587029275478133795469005 34720135978304300173300877)
                  ·
                    refine ⟨13020050991864112564987829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34720135978304300173300877 13020050991864112564987829)
                    ·
                      refine ⟨1220629780487260552967609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13020050991864112564987829 1220629780487260552967609)
                      ·
                        rfl

theorem cell23_2377168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2377168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377168 prefixEnd_2377168 := by exact prefixLift 2377168
  have htrace : WordTrace (prefixWord ++ tailWord_2377168) baseStart_2377168 baseEnd_2377168 := by
    simpa [prefixWord, tailWord_2377168, baseEnd_2377168] using wordTrace_append hprefix tailTrace_2377168
  have hstable : (prefixWord ++ tailWord_2377168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377168).length < 2 ^ (prefixWord ++ tailWord_2377168).sum := by decide
  have hdescent : baseEnd_2377168 < baseStart_2377168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377185 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2377185 : Nat := 118140960795 + 2377185 * 2 ^ 59
def prefixEnd_2377185 : Nat := 4983230072969 + 3 ^ 40 * 2377185 * 2
def baseEnd_2377185 : Nat := 1220638509658386986455031

theorem tailTrace_2377185 : CollatzResearch.WordTrace tailWord_2377185 prefixEnd_2377185 1220638509658386986455031 := by
  unfold tailWord_2377185
  simp only [CollatzResearch.WordTrace]
  refine ⟨86703059892872210720525009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57802039928581473813683339 86703059892872210720525009)
  ·
    refine ⟨65027294919654158040393757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86703059892872210720525009 65027294919654158040393757)
    ·
      refine ⟨24385235594870309265147659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65027294919654158040393757 24385235594870309265147659)
      ·
        refine ⟨36577853392305463897721489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24385235594870309265147659 36577853392305463897721489)
        ·
          refine ⟨27433390044229097923291117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36577853392305463897721489 27433390044229097923291117)
          ·
            refine ⟨10287521266585911721234169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27433390044229097923291117 10287521266585911721234169)
            ·
              refine ⟨7715640949939433790925627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10287521266585911721234169 7715640949939433790925627)
              ·
                refine ⟨11573461424909150686388441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715640949939433790925627 11573461424909150686388441)
                ·
                  refine ⟨8680096068681863014791331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11573461424909150686388441 8680096068681863014791331)
                  ·
                    refine ⟨13020144103022794522186997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8680096068681863014791331 13020144103022794522186997)
                    ·
                      refine ⟨1220638509658386986455031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13020144103022794522186997 1220638509658386986455031)
                      ·
                        rfl

theorem cell23_2377185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2377185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377185 prefixEnd_2377185 := by exact prefixLift 2377185
  have htrace : WordTrace (prefixWord ++ tailWord_2377185) baseStart_2377185 baseEnd_2377185 := by
    simpa [prefixWord, tailWord_2377185, baseEnd_2377185] using wordTrace_append hprefix tailTrace_2377185
  have hstable : (prefixWord ++ tailWord_2377185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377185).length < 2 ^ (prefixWord ++ tailWord_2377185).sum := by decide
  have hdescent : baseEnd_2377185 < baseStart_2377185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377199 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 2, 2, 2]
def baseStart_2377199 : Nat := 118140960795 + 2377199 * 2 ^ 59
def prefixEnd_2377199 : Nat := 4983230072969 + 3 ^ 40 * 2377199 * 2
def baseEnd_2377199 : Nat := 1220645698387549931679967

theorem tailTrace_2377199 : CollatzResearch.WordTrace tailWord_2377199 prefixEnd_2377199 1220645698387549931679967 := by
  unfold tailWord_2377199
  simp only [CollatzResearch.WordTrace]
  refine ⟨86703570514821491111534651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57802380343214327407689767 86703570514821491111534651)
  ·
    refine ⟨130055355772232236667301977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86703570514821491111534651 130055355772232236667301977)
    ·
      refine ⟨97541516829174177500476483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130055355772232236667301977 97541516829174177500476483)
      ·
        refine ⟨146312275243761266250714725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97541516829174177500476483 146312275243761266250714725)
        ·
          refine ⟨27433551608205237422009011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146312275243761266250714725 27433551608205237422009011)
          ·
            refine ⟨41150327412307856133013517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27433551608205237422009011 41150327412307856133013517)
            ·
              refine ⟨15431372779615446049880069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41150327412307856133013517 15431372779615446049880069)
              ·
                refine ⟨2893382396177896134352513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15431372779615446049880069 2893382396177896134352513)
                ·
                  refine ⟨2170036797133422100764385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893382396177896134352513 2170036797133422100764385)
                  ·
                    refine ⟨1627527597850066575573289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2170036797133422100764385 1627527597850066575573289)
                    ·
                      refine ⟨1220645698387549931679967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627527597850066575573289 1220645698387549931679967)
                      ·
                        rfl

theorem cell23_2377199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2, 2].length) (baseStart_2377199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377199 prefixEnd_2377199 := by exact prefixLift 2377199
  have htrace : WordTrace (prefixWord ++ tailWord_2377199) baseStart_2377199 baseEnd_2377199 := by
    simpa [prefixWord, tailWord_2377199, baseEnd_2377199] using wordTrace_append hprefix tailTrace_2377199
  have hstable : (prefixWord ++ tailWord_2377199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377199).length < 2 ^ (prefixWord ++ tailWord_2377199).sum := by decide
  have hdescent : baseEnd_2377199 < baseStart_2377199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377202 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2377202 : Nat := 118140960795 + 2377202 * 2 ^ 59
def prefixEnd_2377202 : Nat := 4983230072969 + 3 ^ 40 * 2377202 * 2
def baseEnd_2377202 : Nat := 1220647238829513419942453

theorem tailTrace_2377202 : CollatzResearch.WordTrace tailWord_2377202 prefixEnd_2377202 1220647238829513419942453 := by
  unfold tailWord_2377202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675919983452655655973465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57802453289207081749262573 21675919983452655655973465)
  ·
    refine ⟨16256939987589491741980099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21675919983452655655973465 16256939987589491741980099)
    ·
      refine ⟨24385409981384237612970149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16256939987589491741980099 24385409981384237612970149)
      ·
        refine ⟨4572264371509544552431903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24385409981384237612970149 4572264371509544552431903)
        ·
          refine ⟨6858396557264316828647855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572264371509544552431903 6858396557264316828647855)
          ·
            refine ⟨10287594835896475242971783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858396557264316828647855 10287594835896475242971783)
            ·
              refine ⟨15431392253844712864457675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10287594835896475242971783 15431392253844712864457675)
              ·
                refine ⟨23147088380767069296686513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15431392253844712864457675 23147088380767069296686513)
                ·
                  refine ⟨17360316285575301972514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23147088380767069296686513 17360316285575301972514885)
                  ·
                    refine ⟨3255059303545369119846541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17360316285575301972514885 3255059303545369119846541)
                    ·
                      refine ⟨1220647238829513419942453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255059303545369119846541 1220647238829513419942453)
                      ·
                        rfl

theorem cell23_2377202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2377202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377202 prefixEnd_2377202 := by exact prefixLift 2377202
  have htrace : WordTrace (prefixWord ++ tailWord_2377202) baseStart_2377202 baseEnd_2377202 := by
    simpa [prefixWord, tailWord_2377202, baseEnd_2377202] using wordTrace_append hprefix tailTrace_2377202
  have hstable : (prefixWord ++ tailWord_2377202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377202).length < 2 ^ (prefixWord ++ tailWord_2377202).sum := by decide
  have hdescent : baseEnd_2377202 < baseStart_2377202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377235 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 7]
def baseStart_2377235 : Nat := 118140960795 + 2377235 * 2 ^ 59
def prefixEnd_2377235 : Nat := 4983230072969 + 3 ^ 40 * 2377235 * 2
def baseEnd_2377235 : Nat := 406888061230370596943267

theorem tailTrace_2377235 : CollatzResearch.WordTrace tailWord_2377235 prefixEnd_2377235 406888061230370596943267 := by
  unfold tailWord_2377235
  simp only [CollatzResearch.WordTrace]
  refine ⟨86704883542691069259845159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57803255695127379506563439 86704883542691069259845159)
  ·
    refine ⟨130057325314036603889767739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86704883542691069259845159 130057325314036603889767739)
    ·
      refine ⟨195085987971054905834651609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130057325314036603889767739 195085987971054905834651609)
      ·
        refine ⟨146314490978291179375988707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195085987971054905834651609 146314490978291179375988707)
        ·
          refine ⟨219471736467436769063983061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146314490978291179375988707 219471736467436769063983061)
          ·
            refine ⟨5143868823455549274937103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 219471736467436769063983061 5143868823455549274937103)
            ·
              refine ⟨7715803235183323912405655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143868823455549274937103 7715803235183323912405655)
              ·
                refine ⟨11573704852774985868608483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715803235183323912405655 11573704852774985868608483)
                ·
                  refine ⟨17360557279162478802912725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11573704852774985868608483 17360557279162478802912725)
                  ·
                    refine ⟨406888061230370596943267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17360557279162478802912725 406888061230370596943267)
                    ·
                      rfl

theorem cell23_2377235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_2377235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377235 prefixEnd_2377235 := by exact prefixLift 2377235
  have htrace : WordTrace (prefixWord ++ tailWord_2377235) baseStart_2377235 baseEnd_2377235 := by
    simpa [prefixWord, tailWord_2377235, baseEnd_2377235] using wordTrace_append hprefix tailTrace_2377235
  have hstable : (prefixWord ++ tailWord_2377235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377235).length < 2 ^ (prefixWord ++ tailWord_2377235).sum := by decide
  have hdescent : baseEnd_2377235 < baseStart_2377235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377285 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2377285 : Nat := 118140960795 + 2377285 * 2 ^ 59
def prefixEnd_2377285 : Nat := 4983230072969 + 3 ^ 40 * 2377285 * 2
def baseEnd_2377285 : Nat := 1220689857723836595204571

theorem tailTrace_2377285 : CollatzResearch.WordTrace tailWord_2377285 prefixEnd_2377285 1220689857723836595204571 := by
  unfold tailWord_2377285
  simp only [CollatzResearch.WordTrace]
  refine ⟨86706707192509927799165309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57804471461673285199443539 86706707192509927799165309)
  ·
    refine ⟨32515015197191222924686991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86706707192509927799165309 32515015197191222924686991)
    ·
      refine ⟨48772522795786834387030487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32515015197191222924686991 48772522795786834387030487)
      ·
        refine ⟨73158784193680251580545731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48772522795786834387030487 73158784193680251580545731)
        ·
          refine ⟨109738176290520377370818597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73158784193680251580545731 109738176290520377370818597)
          ·
            refine ⟨20575908054472570757028487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109738176290520377370818597 20575908054472570757028487)
            ·
              refine ⟨30863862081708856135542731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20575908054472570757028487 30863862081708856135542731)
              ·
                refine ⟨46295793122563284203314097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30863862081708856135542731 46295793122563284203314097)
                ·
                  refine ⟨34721844841922463152485573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46295793122563284203314097 34721844841922463152485573)
                  ·
                    refine ⟨6510345907860461841091045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34721844841922463152485573 6510345907860461841091045)
                    ·
                      refine ⟨1220689857723836595204571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6510345907860461841091045 1220689857723836595204571)
                      ·
                        rfl

theorem cell23_2377285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2377285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377285 prefixEnd_2377285 := by exact prefixLift 2377285
  have htrace : WordTrace (prefixWord ++ tailWord_2377285) baseStart_2377285 baseEnd_2377285 := by
    simpa [prefixWord, tailWord_2377285, baseEnd_2377285] using wordTrace_append hprefix tailTrace_2377285
  have hstable : (prefixWord ++ tailWord_2377285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377285).length < 2 ^ (prefixWord ++ tailWord_2377285).sum := by decide
  have hdescent : baseEnd_2377285 < baseStart_2377285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377292 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2377292 : Nat := 118140960795 + 2377292 * 2 ^ 59
def prefixEnd_2377292 : Nat := 4983230072969 + 3 ^ 40 * 2377292 * 2
def baseEnd_2377292 : Nat := 1220693452088418067817039

theorem tailTrace_2377292 : CollatzResearch.WordTrace tailWord_2377292 prefixEnd_2377292 1220693452088418067817039 := by
  unfold tailWord_2377292
  simp only [CollatzResearch.WordTrace]
  refine ⟨43353481251742283997335065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57804641668989711996446753 43353481251742283997335065)
  ·
    refine ⟨32515110938806712998001299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43353481251742283997335065 32515110938806712998001299)
    ·
      refine ⟨48772666408210069497001949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32515110938806712998001299 48772666408210069497001949)
      ·
        refine ⟨18289749903078776061375731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48772666408210069497001949 18289749903078776061375731)
        ·
          refine ⟨27434624854618164092063597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18289749903078776061375731 27434624854618164092063597)
          ·
            refine ⟨10287984320481811534523849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27434624854618164092063597 10287984320481811534523849)
            ·
              refine ⟨7715988240361358650892887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10287984320481811534523849 7715988240361358650892887)
              ·
                refine ⟨11573982360542037976339331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715988240361358650892887 11573982360542037976339331)
                ·
                  refine ⟨17360973540813056964508997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11573982360542037976339331 17360973540813056964508997)
                  ·
                    refine ⟨3255182538902448180845437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17360973540813056964508997 3255182538902448180845437)
                    ·
                      refine ⟨1220693452088418067817039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255182538902448180845437 1220693452088418067817039)
                      ·
                        rfl

theorem cell23_2377292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2377292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377292 prefixEnd_2377292 := by exact prefixLift 2377292
  have htrace : WordTrace (prefixWord ++ tailWord_2377292) baseStart_2377292 baseEnd_2377292 := by
    simpa [prefixWord, tailWord_2377292, baseEnd_2377292] using wordTrace_append hprefix tailTrace_2377292
  have hstable : (prefixWord ++ tailWord_2377292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377292).length < 2 ^ (prefixWord ++ tailWord_2377292).sum := by decide
  have hdescent : baseEnd_2377292 < baseStart_2377292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377356 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2377356 : Nat := 118140960795 + 2377356 * 2 ^ 59
def prefixEnd_2377356 : Nat := 4983230072969 + 3 ^ 40 * 2377356 * 2
def baseEnd_2377356 : Nat := 1220726314850305817416745

theorem tailTrace_2377356 : CollatzResearch.WordTrace tailWord_2377356 prefixEnd_2377356 1220726314850305817416745 := by
  unfold tailWord_2377356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43354648387626353462499961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57806197850168471283333281 43354648387626353462499961)
  ·
    refine ⟨32515986290719765096874971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43354648387626353462499961 32515986290719765096874971)
    ·
      refine ⟨48773979436079647645312457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32515986290719765096874971 48773979436079647645312457)
      ·
        refine ⟨36580484577059735733984343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48773979436079647645312457 36580484577059735733984343)
        ·
          refine ⟨54870726865589603600976515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36580484577059735733984343 54870726865589603600976515)
          ·
            refine ⟨82306090298384405401464773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54870726865589603600976515 82306090298384405401464773)
            ·
              refine ⟨15432391930947076012774645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82306090298384405401464773 15432391930947076012774645)
              ·
                refine ⟨1446786743526288376197623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15432391930947076012774645 1446786743526288376197623)
                ·
                  refine ⟨2170180115289432564296435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446786743526288376197623 2170180115289432564296435)
                  ·
                    refine ⟨3255270172934148846444653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170180115289432564296435 3255270172934148846444653)
                    ·
                      refine ⟨1220726314850305817416745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255270172934148846444653 1220726314850305817416745)
                      ·
                        rfl

theorem cell23_2377356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2377356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377356 prefixEnd_2377356 := by exact prefixLift 2377356
  have htrace : WordTrace (prefixWord ++ tailWord_2377356) baseStart_2377356 baseEnd_2377356 := by
    simpa [prefixWord, tailWord_2377356, baseEnd_2377356] using wordTrace_append hprefix tailTrace_2377356
  have hstable : (prefixWord ++ tailWord_2377356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377356).length < 2 ^ (prefixWord ++ tailWord_2377356).sum := by decide
  have hdescent : baseEnd_2377356 < baseStart_2377356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377389 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2377389 : Nat := 118140960795 + 2377389 * 2 ^ 59
def prefixEnd_2377389 : Nat := 4983230072969 + 3 ^ 40 * 2377389 * 2
def baseEnd_2377389 : Nat := 406914419903968062768031

theorem tailTrace_2377389 : CollatzResearch.WordTrace tailWord_2377389 prefixEnd_2377389 406914419903968062768031 := by
  unfold tailWord_2377389
  simp only [CollatzResearch.WordTrace]
  refine ⟨86710500384133153560951221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57807000256088769040634147 86710500384133153560951221)
  ·
    refine ⟨8129109411012483146339177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86710500384133153560951221 8129109411012483146339177)
    ·
      refine ⟨6096832058259362359754383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8129109411012483146339177 6096832058259362359754383)
      ·
        refine ⟨9145248087389043539631575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6096832058259362359754383 9145248087389043539631575)
        ·
          refine ⟨13717872131083565309447363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9145248087389043539631575 13717872131083565309447363)
          ·
            refine ⟨20576808196625347964171045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13717872131083565309447363 20576808196625347964171045)
            ·
              refine ⟨3858151536867252743282071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20576808196625347964171045 3858151536867252743282071)
              ·
                refine ⟨5787227305300879114923107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858151536867252743282071 5787227305300879114923107)
                ·
                  refine ⟨8680840957951318672384661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5787227305300879114923107 8680840957951318672384661)
                  ·
                    refine ⟨406914419903968062768031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8680840957951318672384661 406914419903968062768031)
                    ·
                      rfl

theorem cell23_2377389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2377389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377389 prefixEnd_2377389 := by exact prefixLift 2377389
  have htrace : WordTrace (prefixWord ++ tailWord_2377389) baseStart_2377389 baseEnd_2377389 := by
    simpa [prefixWord, tailWord_2377389, baseEnd_2377389] using wordTrace_append hprefix tailTrace_2377389
  have hstable : (prefixWord ++ tailWord_2377389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377389).length < 2 ^ (prefixWord ++ tailWord_2377389).sum := by decide
  have hdescent : baseEnd_2377389 < baseStart_2377389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377392 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_2377392 : Nat := 118140960795 + 2377392 * 2 ^ 59
def prefixEnd_2377392 : Nat := 4983230072969 + 3 ^ 40 * 2377392 * 2
def baseEnd_2377392 : Nat := 1220744800153867676566579

theorem tailTrace_2377392 : CollatzResearch.WordTrace tailWord_2377392 prefixEnd_2377392 1220744800153867676566579 := by
  unfold tailWord_2377392
  simp only [CollatzResearch.WordTrace]
  refine ⟨43355304901561142536655215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57807073202081523382206953 43355304901561142536655215)
  ·
    refine ⟨65032957352341713804982823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43355304901561142536655215 65032957352341713804982823)
    ·
      refine ⟨97549436028512570707474235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65032957352341713804982823 97549436028512570707474235)
      ·
        refine ⟨146324154042768856061211353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97549436028512570707474235 146324154042768856061211353)
        ·
          refine ⟨109743115532076642045908515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146324154042768856061211353 109743115532076642045908515)
          ·
            refine ⟨164614673298114963068862773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109743115532076642045908515 164614673298114963068862773)
            ·
              refine ⟨15432625621698277787705885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164614673298114963068862773 15432625621698277787705885)
              ·
                refine ⟨5787234608136854170389707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15432625621698277787705885 5787234608136854170389707)
                ·
                  refine ⟨8680851912205281255584561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5787234608136854170389707 8680851912205281255584561)
                  ·
                    refine ⟨6510638934153960941688421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8680851912205281255584561 6510638934153960941688421)
                    ·
                      refine ⟨1220744800153867676566579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6510638934153960941688421 1220744800153867676566579)
                      ·
                        rfl

theorem cell23_2377392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_2377392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377392 prefixEnd_2377392 := by exact prefixLift 2377392
  have htrace : WordTrace (prefixWord ++ tailWord_2377392) baseStart_2377392 baseEnd_2377392 := by
    simpa [prefixWord, tailWord_2377392, baseEnd_2377392] using wordTrace_append hprefix tailTrace_2377392
  have hstable : (prefixWord ++ tailWord_2377392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377392).length < 2 ^ (prefixWord ++ tailWord_2377392).sum := by decide
  have hdescent : baseEnd_2377392 < baseStart_2377392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377399 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_2377399 : Nat := 118140960795 + 2377399 * 2 ^ 59
def prefixEnd_2377399 : Nat := 4983230072969 + 3 ^ 40 * 2377399 * 2
def baseEnd_2377399 : Nat := 1220748394518449149179047

theorem tailTrace_2377399 : CollatzResearch.WordTrace tailWord_2377399 prefixEnd_2377399 1220748394518449149179047 := by
  unfold tailWord_2377399
  simp only [CollatzResearch.WordTrace]
  refine ⟨86710865114096925268815251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57807243409397950179210167 86710865114096925268815251)
  ·
    refine ⟨130066297671145387903222877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86710865114096925268815251 130066297671145387903222877)
    ·
      refine ⟨48774861626679520463708579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130066297671145387903222877 48774861626679520463708579)
      ·
        refine ⟨73162292440019280695562869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48774861626679520463708579 73162292440019280695562869)
        ·
          refine ⟨6858964916251807565209019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73162292440019280695562869 6858964916251807565209019)
          ·
            refine ⟨10288447374377711347813529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858964916251807565209019 10288447374377711347813529)
            ·
              refine ⟨7716335530783283510860147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10288447374377711347813529 7716335530783283510860147)
              ·
                refine ⟨11574503296174925266290221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716335530783283510860147 11574503296174925266290221)
                ·
                  refine ⟨4340438736065596974858833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11574503296174925266290221 4340438736065596974858833)
                  ·
                    refine ⟨3255329052049197731144125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340438736065596974858833 3255329052049197731144125)
                    ·
                      refine ⟨1220748394518449149179047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3255329052049197731144125 1220748394518449149179047)
                      ·
                        rfl

theorem cell23_2377399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_2377399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377399 prefixEnd_2377399 := by exact prefixLift 2377399
  have htrace : WordTrace (prefixWord ++ tailWord_2377399) baseStart_2377399 baseEnd_2377399 := by
    simpa [prefixWord, tailWord_2377399, baseEnd_2377399] using wordTrace_append hprefix tailTrace_2377399
  have hstable : (prefixWord ++ tailWord_2377399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377399).length < 2 ^ (prefixWord ++ tailWord_2377399).sum := by decide
  have hdescent : baseEnd_2377399 < baseStart_2377399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377410 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2377410 : Nat := 118140960795 + 2377410 * 2 ^ 59
def prefixEnd_2377410 : Nat := 4983230072969 + 3 ^ 40 * 2377410 * 2
def baseEnd_2377410 : Nat := 406918014268549535380499

theorem tailTrace_2377410 : CollatzResearch.WordTrace tailWord_2377410 prefixEnd_2377410 406918014268549535380499 := by
  unfold tailWord_2377410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21677816579264268536866421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57807510878038049431643789 21677816579264268536866421)
  ·
    refine ⟨2032295304306025175331227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21677816579264268536866421 2032295304306025175331227)
    ·
      refine ⟨3048442956459037762996841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032295304306025175331227 3048442956459037762996841)
      ·
        refine ⟨2286332217344278322247631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3048442956459037762996841 2286332217344278322247631)
        ·
          refine ⟨3429498326016417483371447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286332217344278322247631 3429498326016417483371447)
          ·
            refine ⟨5144247489024626225057171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429498326016417483371447 5144247489024626225057171)
            ·
              refine ⟨7716371233536939337585757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144247489024626225057171 7716371233536939337585757)
              ·
                refine ⟨2893639212576352251594659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7716371233536939337585757 2893639212576352251594659)
                ·
                  refine ⟨4340458818864528377391989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893639212576352251594659 4340458818864528377391989)
                  ·
                    refine ⟨406918014268549535380499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4340458818864528377391989 406918014268549535380499)
                    ·
                      rfl

theorem cell23_2377410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2377410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377410 prefixEnd_2377410 := by exact prefixLift 2377410
  have htrace : WordTrace (prefixWord ++ tailWord_2377410) baseStart_2377410 baseEnd_2377410 := by
    simpa [prefixWord, tailWord_2377410, baseEnd_2377410] using wordTrace_append hprefix tailTrace_2377410
  have hstable : (prefixWord ++ tailWord_2377410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377410).length < 2 ^ (prefixWord ++ tailWord_2377410).sum := by decide
  have hdescent : baseEnd_2377410 < baseStart_2377410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377443 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2377443 : Nat := 118140960795 + 2377443 * 2 ^ 59
def prefixEnd_2377443 : Nat := 4983230072969 + 3 ^ 40 * 2377443 * 2
def baseEnd_2377443 : Nat := 1220770987667246977028845

theorem tailTrace_2377443 : CollatzResearch.WordTrace tailWord_2377443 prefixEnd_2377443 1220770987667246977028845 := by
  unfold tailWord_2377443
  simp only [CollatzResearch.WordTrace]
  refine ⟨86712469925937520783416983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57808313283958347188944655 86712469925937520783416983)
  ·
    refine ⟨130068704888906281175125475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86712469925937520783416983 130068704888906281175125475)
    ·
      refine ⟨195103057333359421762688213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130068704888906281175125475 195103057333359421762688213)
      ·
        refine ⟨4572727906250611447563005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 195103057333359421762688213 4572727906250611447563005)
        ·
          refine ⟨1714772964843979292836127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4572727906250611447563005 1714772964843979292836127)
          ·
            refine ⟨2572159447265968939254191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714772964843979292836127 2572159447265968939254191)
            ·
              refine ⟨3858239170898953408881287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572159447265968939254191 3858239170898953408881287)
              ·
                refine ⟨5787358756348430113321931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858239170898953408881287 5787358756348430113321931)
                ·
                  refine ⟨8681038134522645169982897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5787358756348430113321931 8681038134522645169982897)
                  ·
                    refine ⟨6510778600891983877487173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8681038134522645169982897 6510778600891983877487173)
                    ·
                      refine ⟨1220770987667246977028845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6510778600891983877487173 1220770987667246977028845)
                      ·
                        rfl

theorem cell23_2377443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2377443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377443 prefixEnd_2377443 := by exact prefixLift 2377443
  have htrace : WordTrace (prefixWord ++ tailWord_2377443) baseStart_2377443 baseEnd_2377443 := by
    simpa [prefixWord, tailWord_2377443, baseEnd_2377443] using wordTrace_append hprefix tailTrace_2377443
  have hstable : (prefixWord ++ tailWord_2377443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377443).length < 2 ^ (prefixWord ++ tailWord_2377443).sum := by decide
  have hdescent : baseEnd_2377443 < baseStart_2377443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377452 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2377452 : Nat := 118140960795 + 2377452 * 2 ^ 59
def prefixEnd_2377452 : Nat := 4983230072969 + 3 ^ 40 * 2377452 * 2
def baseEnd_2377452 : Nat := 1220775608993137441816303

theorem tailTrace_2377452 : CollatzResearch.WordTrace tailWord_2377452 prefixEnd_2377452 1220775608993137441816303 := by
  unfold tailWord_2377452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43356399091452457660247305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57808532121936610213663073 43356399091452457660247305)
  ·
    refine ⟨32517299318589343245185479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43356399091452457660247305 32517299318589343245185479)
    ·
      refine ⟨48775948977884014867778219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32517299318589343245185479 48775948977884014867778219)
      ·
        refine ⟨73163923466826022301667329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48775948977884014867778219 73163923466826022301667329)
        ·
          refine ⟨54872942600119516726250497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73163923466826022301667329 54872942600119516726250497)
          ·
            refine ⟨41154706950089637544687873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54872942600119516726250497 41154706950089637544687873)
            ·
              refine ⟨30866030212567228158515905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41154706950089637544687873 30866030212567228158515905)
              ·
                refine ⟨23149522659425421118886929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30866030212567228158515905 23149522659425421118886929)
                ·
                  refine ⟨17362141994569065839165197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23149522659425421118886929 17362141994569065839165197)
                  ·
                    refine ⟨6510803247963399689686949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17362141994569065839165197 6510803247963399689686949)
                    ·
                      refine ⟨1220775608993137441816303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6510803247963399689686949 1220775608993137441816303)
                      ·
                        rfl

theorem cell23_2377452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2377452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377452 prefixEnd_2377452 := by exact prefixLift 2377452
  have htrace : WordTrace (prefixWord ++ tailWord_2377452) baseStart_2377452 baseEnd_2377452 := by
    simpa [prefixWord, tailWord_2377452, baseEnd_2377452] using wordTrace_append hprefix tailTrace_2377452
  have hstable : (prefixWord ++ tailWord_2377452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377452).length < 2 ^ (prefixWord ++ tailWord_2377452).sum := by decide
  have hdescent : baseEnd_2377452 < baseStart_2377452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377472 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2377472 : Nat := 118140960795 + 2377472 * 2 ^ 59
def prefixEnd_2377472 : Nat := 4983230072969 + 3 ^ 40 * 2377472 * 2
def baseEnd_2377472 : Nat := 1220785878606227363566211

theorem tailTrace_2377472 : CollatzResearch.WordTrace tailWord_2377472 prefixEnd_2377472 1220785878606227363566211 := by
  unfold tailWord_2377472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43356763821416229368111335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57809018428554972490815113 43356763821416229368111335)
  ·
    refine ⟨65035145732124344052167003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43356763821416229368111335 65035145732124344052167003)
    ·
      refine ⟨97552718598186516078250505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65035145732124344052167003 97552718598186516078250505)
      ·
        refine ⟨73164538948639887058687879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97552718598186516078250505 73164538948639887058687879)
        ·
          refine ⟨109746808422959830588031819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73164538948639887058687879 109746808422959830588031819)
          ·
            refine ⟨164620212634439745882047729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109746808422959830588031819 164620212634439745882047729)
            ·
              refine ⟨123465159475829809411535797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164620212634439745882047729 123465159475829809411535797)
              ·
                refine ⟨11574858700859044632331481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123465159475829809411535797 11574858700859044632331481)
                ·
                  refine ⟨8681144025644283474248611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11574858700859044632331481 8681144025644283474248611)
                  ·
                    refine ⟨13021716038466425211372917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8681144025644283474248611 13021716038466425211372917)
                    ·
                      refine ⟨1220785878606227363566211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13021716038466425211372917 1220785878606227363566211)
                      ·
                        rfl

theorem cell23_2377472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2377472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377472 prefixEnd_2377472 := by exact prefixLift 2377472
  have htrace : WordTrace (prefixWord ++ tailWord_2377472) baseStart_2377472 baseEnd_2377472 := by
    simpa [prefixWord, tailWord_2377472, baseEnd_2377472] using wordTrace_append hprefix tailTrace_2377472
  have hstable : (prefixWord ++ tailWord_2377472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377472).length < 2 ^ (prefixWord ++ tailWord_2377472).sum := by decide
  have hdescent : baseEnd_2377472 < baseStart_2377472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377503 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 2, 2, 2]
def baseStart_2377503 : Nat := 118140960795 + 2377503 * 2 ^ 59
def prefixEnd_2377503 : Nat := 4983230072969 + 3 ^ 40 * 2377503 * 2
def baseEnd_2377503 : Nat := 1220801796506516742278569

theorem tailTrace_2377503 : CollatzResearch.WordTrace tailWord_2377503 prefixEnd_2377503 1220801796506516742278569 := by
  unfold tailWord_2377503
  simp only [CollatzResearch.WordTrace]
  refine ⟨86714658305720151030601163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57809772203813434020400775 86714658305720151030601163)
  ·
    refine ⟨130071987458580226545901745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86714658305720151030601163 130071987458580226545901745)
    ·
      refine ⟨97553990593935169909426309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130071987458580226545901745 97553990593935169909426309)
      ·
        refine ⟨18291373236362844358017433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97553990593935169909426309 18291373236362844358017433)
        ·
          refine ⟨13718529927272133268513075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18291373236362844358017433 13718529927272133268513075)
          ·
            refine ⟨20577794890908199902769613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13718529927272133268513075 20577794890908199902769613)
            ·
              refine ⟨7716673084090574963538605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20577794890908199902769613 7716673084090574963538605)
              ·
                refine ⟨2893752406533965611326977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7716673084090574963538605 2893752406533965611326977)
                ·
                  refine ⟨2170314304900474208495233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893752406533965611326977 2170314304900474208495233)
                  ·
                    refine ⟨1627735728675355656371425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2170314304900474208495233 1627735728675355656371425)
                    ·
                      refine ⟨1220801796506516742278569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627735728675355656371425 1220801796506516742278569)
                      ·
                        rfl

theorem cell23_2377503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_2377503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377503 prefixEnd_2377503 := by exact prefixLift 2377503
  have htrace : WordTrace (prefixWord ++ tailWord_2377503) baseStart_2377503 baseEnd_2377503 := by
    simpa [prefixWord, tailWord_2377503, baseEnd_2377503] using wordTrace_append hprefix tailTrace_2377503
  have hstable : (prefixWord ++ tailWord_2377503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377503).length < 2 ^ (prefixWord ++ tailWord_2377503).sum := by decide
  have hdescent : baseEnd_2377503 < baseStart_2377503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377539 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 2, 5]
def baseStart_2377539 : Nat := 118140960795 + 2377539 * 2 ^ 59
def prefixEnd_2377539 : Nat := 4983230072969 + 3 ^ 40 * 2377539 * 2
def baseEnd_2377539 : Nat := 406940093936692867142801

theorem tailTrace_2377539 : CollatzResearch.WordTrace tailWord_2377539 prefixEnd_2377539 406940093936692867142801 := by
  unfold tailWord_2377539
  simp only [CollatzResearch.WordTrace]
  refine ⟨86715971333589729178911671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57810647555726486119274447 86715971333589729178911671)
  ·
    refine ⟨130073957000384593768367507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86715971333589729178911671 130073957000384593768367507)
    ·
      refine ⟨195110935500576890652551261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130073957000384593768367507 195110935500576890652551261)
      ·
        refine ⟨73166600812716333994706723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195110935500576890652551261 73166600812716333994706723)
        ·
          refine ⟨109749901219074500992060085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73166600812716333994706723 109749901219074500992060085)
          ·
            refine ⟨10289053239288234468005633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109749901219074500992060085 10289053239288234468005633)
            ·
              refine ⟨7716789929466175851004225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10289053239288234468005633 7716789929466175851004225)
              ·
                refine ⟨5787592447099631888253169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7716789929466175851004225 5787592447099631888253169)
                ·
                  refine ⟨4340694335324723916189877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5787592447099631888253169 4340694335324723916189877)
                  ·
                    refine ⟨406940093936692867142801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4340694335324723916189877 406940093936692867142801)
                    ·
                      rfl

theorem cell23_2377539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].length) (baseStart_2377539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377539 prefixEnd_2377539 := by exact prefixLift 2377539
  have htrace : WordTrace (prefixWord ++ tailWord_2377539) baseStart_2377539 baseEnd_2377539 := by
    simpa [prefixWord, tailWord_2377539, baseEnd_2377539] using wordTrace_append hprefix tailTrace_2377539
  have hstable : (prefixWord ++ tailWord_2377539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377539).length < 2 ^ (prefixWord ++ tailWord_2377539).sum := by decide
  have hdescent : baseEnd_2377539 < baseStart_2377539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377552 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_2377552 : Nat := 118140960795 + 2377552 * 2 ^ 59
def prefixEnd_2377552 : Nat := 4983230072969 + 3 ^ 40 * 2377552 * 2
def baseEnd_2377552 : Nat := 406942319019529016855281

theorem tailTrace_2377552 : CollatzResearch.WordTrace tailWord_2377552 prefixEnd_2377552 406942319019529016855281 := by
  unfold tailWord_2377552
  simp only [CollatzResearch.WordTrace]
  refine ⟨43358222741271316199567455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57810963655028421599423273 43358222741271316199567455)
  ·
    refine ⟨65037334111906974299351183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43358222741271316199567455 65037334111906974299351183)
    ·
      refine ⟨97556001167860461449026775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65037334111906974299351183 97556001167860461449026775)
      ·
        refine ⟨146334001751790692173540163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97556001167860461449026775 146334001751790692173540163)
        ·
          refine ⟨219501002627686038260310245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146334001751790692173540163 219501002627686038260310245)
          ·
            refine ⟨41156437992691132173808171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219501002627686038260310245 41156437992691132173808171)
            ·
              refine ⟨61734656989036698260712257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41156437992691132173808171 61734656989036698260712257)
              ·
                refine ⟨46300992741777523695534193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61734656989036698260712257 46300992741777523695534193)
                ·
                  refine ⟨34725744556333142771650645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46300992741777523695534193 34725744556333142771650645)
                  ·
                    refine ⟨406942319019529016855281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34725744556333142771650645 406942319019529016855281)
                    ·
                      rfl

theorem cell23_2377552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_2377552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377552 prefixEnd_2377552 := by exact prefixLift 2377552
  have htrace : WordTrace (prefixWord ++ tailWord_2377552) baseStart_2377552 baseEnd_2377552 := by
    simpa [prefixWord, tailWord_2377552, baseEnd_2377552] using wordTrace_append hprefix tailTrace_2377552
  have hstable : (prefixWord ++ tailWord_2377552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377552).length < 2 ^ (prefixWord ++ tailWord_2377552).sum := by decide
  have hdescent : baseEnd_2377552 < baseStart_2377552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377576 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2377576 : Nat := 118140960795 + 2377576 * 2 ^ 59
def prefixEnd_2377576 : Nat := 4983230072969 + 3 ^ 40 * 2377576 * 2
def baseEnd_2377576 : Nat := 1220839280594294956665733

theorem tailTrace_2377576 : CollatzResearch.WordTrace tailWord_2377576 prefixEnd_2377576 1220839280594294956665733 := by
  unfold tailWord_2377576
  simp only [CollatzResearch.WordTrace]
  refine ⟨43358660417227842249004291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57811547222970456332005721 43358660417227842249004291)
  ·
    refine ⟨65037990625841763373506437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43358660417227842249004291 65037990625841763373506437)
    ·
      refine ⟨12194623242345330632532457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65037990625841763373506437 12194623242345330632532457)
      ·
        refine ⟨9145967431758997974399343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12194623242345330632532457 9145967431758997974399343)
        ·
          refine ⟨13718951147638496961599015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9145967431758997974399343 13718951147638496961599015)
          ·
            refine ⟨20578426721457745442398523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13718951147638496961599015 20578426721457745442398523)
            ·
              refine ⟨30867640082186618163597785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20578426721457745442398523 30867640082186618163597785)
              ·
                refine ⟨23150730061639963622698339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30867640082186618163597785 23150730061639963622698339)
                ·
                  refine ⟨34726095092459945434047509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23150730061639963622698339 34726095092459945434047509)
                  ·
                    refine ⟨1627785707459059942220977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34726095092459945434047509 1627785707459059942220977)
                    ·
                      refine ⟨1220839280594294956665733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1627785707459059942220977 1220839280594294956665733)
                      ·
                        rfl

theorem cell23_2377576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2377576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377576 prefixEnd_2377576 := by exact prefixLift 2377576
  have htrace : WordTrace (prefixWord ++ tailWord_2377576) baseStart_2377576 baseEnd_2377576 := by
    simpa [prefixWord, tailWord_2377576, baseEnd_2377576] using wordTrace_append hprefix tailTrace_2377576
  have hstable : (prefixWord ++ tailWord_2377576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377576).length < 2 ^ (prefixWord ++ tailWord_2377576).sum := by decide
  have hdescent : baseEnd_2377576 < baseStart_2377576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377589 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2377589 : Nat := 118140960795 + 2377589 * 2 ^ 59
def prefixEnd_2377589 : Nat := 4983230072969 + 3 ^ 40 * 2377589 * 2
def baseEnd_2377589 : Nat := 1220845955842803405803173

theorem tailTrace_2377589 : CollatzResearch.WordTrace tailWord_2377589 prefixEnd_2377589 1220845955842803405803173 := by
  unfold tailWord_2377589
  simp only [CollatzResearch.WordTrace]
  refine ⟨86717794983408587718231821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57811863322272391812154547 86717794983408587718231821)
  ·
    refine ⟨32519173118778220394336933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86717794983408587718231821 32519173118778220394336933)
    ·
      refine ⟨6097344959770916323938175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32519173118778220394336933 6097344959770916323938175)
      ·
        refine ⟨9146017439656374485907263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097344959770916323938175 9146017439656374485907263)
        ·
          refine ⟨13719026159484561728860895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146017439656374485907263 13719026159484561728860895)
          ·
            refine ⟨20578539239226842593291343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719026159484561728860895 20578539239226842593291343)
            ·
              refine ⟨30867808858840263889937015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20578539239226842593291343 30867808858840263889937015)
              ·
                refine ⟨46301713288260395834905523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30867808858840263889937015 46301713288260395834905523)
                ·
                  refine ⟨69452569932390593752358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46301713288260395834905523 69452569932390593752358285)
                  ·
                    refine ⟨26044713724646472657134357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69452569932390593752358285 26044713724646472657134357)
                    ·
                      refine ⟨1220845955842803405803173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26044713724646472657134357 1220845955842803405803173)
                      ·
                        rfl

theorem cell23_2377589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2377589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2377589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2377589 prefixEnd_2377589 := by exact prefixLift 2377589
  have htrace : WordTrace (prefixWord ++ tailWord_2377589) baseStart_2377589 baseEnd_2377589 := by
    simpa [prefixWord, tailWord_2377589, baseEnd_2377589] using wordTrace_append hprefix tailTrace_2377589
  have hstable : (prefixWord ++ tailWord_2377589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377589).length < 2 ^ (prefixWord ++ tailWord_2377589).sum := by decide
  have hdescent : baseEnd_2377589 < baseStart_2377589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
